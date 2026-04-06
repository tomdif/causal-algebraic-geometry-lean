#!/usr/bin/env python3
"""
Test chamber spectral theory on real LLM attention matrices (GPT-2) or synthetic fallback.

Theory predictions for causal (triangular) attention kernel K = A + A^T - I:
  1. Parity pairing: lambda_2^even = lambda_1^odd under reflection R
  2. Boundary outlier eigenvalues (attention sink at first/last tokens)
  3. Arcsine bulk eigenvalue distribution
"""

import numpy as np
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

# ─── Attempt to load GPT-2; fall back to synthetic ───
USE_GPT2 = False
try:
    from transformers import GPT2Model, GPT2Tokenizer
    import torch
    USE_GPT2 = True
    print("Using real GPT-2 attention matrices.")
except ImportError:
    print("transformers not available. Using synthetic causal attention matrices.\n")


def get_gpt2_attention_matrices(text):
    """Extract attention matrices from GPT-2 for a given text."""
    tokenizer = GPT2Tokenizer.from_pretrained('gpt2')
    model = GPT2Model.from_pretrained('gpt2', output_attentions=True)
    model.eval()
    inputs = tokenizer(text, return_tensors='pt')
    seq_len = inputs['input_ids'].shape[1]
    with torch.no_grad():
        outputs = model(**inputs)
    # outputs.attentions: tuple of (1, n_heads, seq_len, seq_len) per layer
    all_attn = []
    for layer_idx, layer_attn in enumerate(outputs.attentions):
        # shape: (1, 12, seq_len, seq_len)
        A_layer = layer_attn[0].numpy()  # (12, seq_len, seq_len)
        for head_idx in range(A_layer.shape[0]):
            all_attn.append({
                'layer': layer_idx,
                'head': head_idx,
                'A': A_layer[head_idx]  # (seq_len, seq_len)
            })
    return all_attn, seq_len


def get_synthetic_attention_matrices(m=30, n_matrices=24, seed=42):
    """Generate synthetic causal attention matrices via softmax of masked random logits."""
    rng = np.random.RandomState(seed)
    mask = np.tril(np.ones((m, m)))  # lower triangular = causal (attends to past)
    all_attn = []
    for i in range(n_matrices):
        logits = rng.randn(m, m) * 0.5
        logits = logits * mask + (1 - mask) * (-1e9)
        A = np.exp(logits) / np.exp(logits).sum(axis=-1, keepdims=True)
        all_attn.append({
            'layer': i // 12,
            'head': i % 12,
            'A': A
        })
    return all_attn, m


def build_reflection(m):
    """Build the reflection matrix R[i,j] = delta_{i, m-1-j}."""
    R = np.zeros((m, m))
    for i in range(m):
        R[i, m - 1 - i] = 1.0
    return R


def get_sector_bases(R):
    """
    Get orthonormal bases for R-even (+1 eigenspace) and R-odd (-1 eigenspace).
    Returns V_plus, V_minus as column matrices.
    """
    m = R.shape[0]
    evals, evecs = np.linalg.eigh(R)
    # R is symmetric with eigenvalues +1 and -1
    plus_mask = evals > 0.5
    minus_mask = evals < -0.5
    V_plus = evecs[:, plus_mask]
    V_minus = evecs[:, minus_mask]
    return V_plus, V_minus


def symmetrize_variants(A):
    """Return dict of symmetrization variants of attention matrix A."""
    m = A.shape[0]
    I = np.eye(m)
    K1 = A + A.T
    K2 = A + A.T - I
    K3 = A + A.T - np.diag(np.diag(A + A.T))  # Laplacian-like
    K4 = (A + A.T) / 2
    return {'K1=A+A^T': K1, 'K2=A+A^T-I': K2, 'K3=Laplacian': K3, 'K4=(A+A^T)/2': K4}


def parity_pairing_error(K, V_plus, V_minus):
    """
    Compute parity pairing: compare lambda_2^even with lambda_1^odd.
    Returns relative error |lambda_2_even - lambda_1_odd| / max(|lambda_2_even|, |lambda_1_odd|).
    """
    K_plus = V_plus.T @ K @ V_plus
    K_minus = V_minus.T @ K @ V_minus
    evals_plus = np.sort(np.linalg.eigvalsh(K_plus))[::-1]  # descending
    evals_minus = np.sort(np.linalg.eigvalsh(K_minus))[::-1]

    if len(evals_plus) < 2 or len(evals_minus) < 1:
        return np.nan, evals_plus, evals_minus

    lam2_even = evals_plus[1]
    lam1_odd = evals_minus[0]
    denom = max(abs(lam2_even), abs(lam1_odd), 1e-15)
    rel_err = abs(lam2_even - lam1_odd) / denom
    return rel_err, evals_plus, evals_minus


def attention_sink_test(K):
    """
    Test whether top eigenvector concentrates on first/last tokens.
    Returns: weight on token 0, weight on last token, uniform baseline.
    """
    m = K.shape[0]
    evals, evecs = np.linalg.eigh(K)
    top_idx = np.argmax(evals)
    top_vec = evecs[:, top_idx]
    top_vec_sq = top_vec ** 2  # probability weights

    w_first = top_vec_sq[0]
    w_last = top_vec_sq[-1]
    w_first3 = top_vec_sq[:3].sum()
    w_last3 = top_vec_sq[-3:].sum()
    uniform = 1.0 / m

    return {
        'w_first': w_first,
        'w_last': w_last,
        'w_first3': w_first3,
        'w_last3': w_last3,
        'uniform': uniform,
        'top_eigenvalue': evals[top_idx],
        'profile': top_vec_sq
    }


def bulk_arcsine_test(evals_odd_all):
    """
    Test whether the bulk eigenvalues follow arcsine distribution.
    Normalize to [-1, 1] and compare with arcsine CDF.
    """
    if len(evals_odd_all) < 10:
        return {'ks_stat': np.nan, 'ks_pvalue': np.nan}

    vals = np.array(evals_odd_all)
    # Remove outliers (top/bottom 5%)
    lo, hi = np.percentile(vals, 5), np.percentile(vals, 95)
    bulk = vals[(vals >= lo) & (vals <= hi)]
    if len(bulk) < 10:
        return {'ks_stat': np.nan, 'ks_pvalue': np.nan}

    # Normalize to [-1, 1]
    mid = (bulk.max() + bulk.min()) / 2
    span = (bulk.max() - bulk.min()) / 2
    if span < 1e-15:
        return {'ks_stat': np.nan, 'ks_pvalue': np.nan}
    normed = (bulk - mid) / span

    # Arcsine distribution on [-1,1]: CDF = 0.5 + arcsin(x)/pi
    ks_stat, ks_pvalue = stats.kstest(normed, lambda x: 0.5 + np.arcsin(np.clip(x, -1, 1)) / np.pi)
    return {'ks_stat': ks_stat, 'ks_pvalue': ks_pvalue, 'n_bulk': len(bulk)}


# ─── Main ───
def run_experiment(texts=None):
    if texts is None:
        texts = [
            "The quick brown fox jumps over the lazy dog and then runs away quickly",
            "In the beginning God created the heavens and the earth and the earth was formless",
            "Machine learning models have transformed natural language processing in recent years",
            "A long time ago in a galaxy far far away there lived a young warrior",
            "The eigenvalues of a symmetric matrix are always real and the eigenvectors orthogonal",
        ]

    all_results = {name: [] for name in ['K1=A+A^T', 'K2=A+A^T-I', 'K3=Laplacian', 'K4=(A+A^T)/2']}
    all_sink_results = []
    all_odd_evals = {name: [] for name in all_results}
    all_parity_by_layer = {}

    for text_idx, text in enumerate(texts):
        print(f"\n{'='*70}")
        print(f"Input {text_idx+1}: \"{text[:60]}...\"")
        print('='*70)

        if USE_GPT2:
            attn_list, m = get_gpt2_attention_matrices(text)
        else:
            m = 15 + text_idx * 3  # vary sequence length
            attn_list, m = get_synthetic_attention_matrices(m=m, n_matrices=24, seed=42+text_idx)

        R = build_reflection(m)
        V_plus, V_minus = get_sector_bases(R)
        print(f"  Sequence length: {m}")
        print(f"  Even sector dim: {V_plus.shape[1]}, Odd sector dim: {V_minus.shape[1]}")
        print(f"  Number of attention matrices: {len(attn_list)}")

        for attn_info in attn_list:
            A = attn_info['A']
            layer, head = attn_info['layer'], attn_info['head']
            variants = symmetrize_variants(A)

            for name, K in variants.items():
                rel_err, evals_plus, evals_minus = parity_pairing_error(K, V_plus, V_minus)
                all_results[name].append(rel_err)
                all_odd_evals[name].extend(evals_minus.tolist())

                key = (name, layer)
                if key not in all_parity_by_layer:
                    all_parity_by_layer[key] = []
                all_parity_by_layer[key].append(rel_err)

            # Attention sink test on K1
            K1 = variants['K1=A+A^T']
            sink = attention_sink_test(K1)
            all_sink_results.append(sink)

    # ─── REPORT ───
    print("\n" + "="*70)
    print("RESULTS SUMMARY")
    print("="*70)

    # 1. Parity pairing
    print("\n--- PARITY PAIRING: |lambda_2^even - lambda_1^odd| / max ---")
    print(f"{'Normalization':<20} {'Mean':>8} {'Std':>8} {'Median':>8} {'<1%':>6} {'<5%':>6} {'<10%':>6}")
    print("-" * 70)
    best_name, best_mean = None, 1e10
    for name in all_results:
        errs = np.array(all_results[name])
        errs = errs[~np.isnan(errs)]
        if len(errs) == 0:
            continue
        mean_e = np.mean(errs)
        std_e = np.std(errs)
        med_e = np.median(errs)
        frac_1 = np.mean(errs < 0.01) * 100
        frac_5 = np.mean(errs < 0.05) * 100
        frac_10 = np.mean(errs < 0.10) * 100
        print(f"{name:<20} {mean_e:>8.4f} {std_e:>8.4f} {med_e:>8.4f} {frac_1:>5.1f}% {frac_5:>5.1f}% {frac_10:>5.1f}%")
        if mean_e < best_mean:
            best_mean = mean_e
            best_name = name
    print(f"\nBest normalization: {best_name} (mean relative error = {best_mean:.4f})")

    # 2. Parity by layer
    print("\n--- PARITY PAIRING BY LAYER (best normalization: {}) ---".format(best_name))
    layers_seen = sorted(set(k[1] for k in all_parity_by_layer if k[0] == best_name))
    for layer in layers_seen:
        errs = all_parity_by_layer[(best_name, layer)]
        errs = np.array(errs)
        errs = errs[~np.isnan(errs)]
        if len(errs) > 0:
            print(f"  Layer {layer:>2d}: mean={np.mean(errs):.4f}, median={np.median(errs):.4f}, "
                  f"min={np.min(errs):.4f}, max={np.max(errs):.4f}")

    # 3. Attention sink
    print("\n--- ATTENTION SINK (K1 = A + A^T) ---")
    w_firsts = [s['w_first'] for s in all_sink_results]
    w_lasts = [s['w_last'] for s in all_sink_results]
    w_f3 = [s['w_first3'] for s in all_sink_results]
    w_l3 = [s['w_last3'] for s in all_sink_results]
    uniform = all_sink_results[0]['uniform']
    print(f"  Uniform baseline: {uniform:.4f}")
    print(f"  First token weight:  mean={np.mean(w_firsts):.4f}, std={np.std(w_firsts):.4f}, "
          f"max={np.max(w_firsts):.4f}")
    print(f"  Last token weight:   mean={np.mean(w_lasts):.4f}, std={np.std(w_lasts):.4f}, "
          f"max={np.max(w_lasts):.4f}")
    print(f"  First 3 tokens:      mean={np.mean(w_f3):.4f}")
    print(f"  Last 3 tokens:       mean={np.mean(w_l3):.4f}")
    ratio_first = np.mean(w_firsts) / uniform
    ratio_last = np.mean(w_lasts) / uniform
    print(f"  First token / uniform = {ratio_first:.2f}x")
    print(f"  Last token / uniform  = {ratio_last:.2f}x")
    if ratio_first > 2.0:
        print("  --> CONFIRMED: Attention sink at first token (>2x uniform)")
    elif ratio_first > 1.5:
        print("  --> WEAK: Mild concentration at first token (1.5-2x uniform)")
    else:
        print("  --> NOT CONFIRMED: No significant attention sink at first token")

    # 4. Bulk arcsine test
    print("\n--- BULK EIGENVALUE DISTRIBUTION (odd sector) ---")
    for name in all_odd_evals:
        result = bulk_arcsine_test(all_odd_evals[name])
        if not np.isnan(result['ks_stat']):
            print(f"  {name:<20}: KS stat={result['ks_stat']:.4f}, p-value={result['ks_pvalue']:.4f}, "
                  f"n={result.get('n_bulk', '?')}")
            if result['ks_pvalue'] > 0.05:
                print(f"    --> Consistent with arcsine (p > 0.05)")
            else:
                print(f"    --> NOT arcsine (p < 0.05)")

    # 5. Detailed eigenvalue spectrum for one example
    print("\n--- SAMPLE EIGENVALUE SPECTRUM (first matrix, best normalization) ---")
    if USE_GPT2:
        attn_list, m = get_gpt2_attention_matrices(texts[0])
    else:
        attn_list, m = get_synthetic_attention_matrices(m=20, n_matrices=1, seed=42)
    R = build_reflection(m)
    V_plus, V_minus = get_sector_bases(R)
    A = attn_list[0]['A']
    K = symmetrize_variants(A)[best_name]
    _, evals_plus, evals_minus = parity_pairing_error(K, V_plus, V_minus)
    print(f"  Even sector eigenvalues (top 8): {evals_plus[:8]}")
    print(f"  Odd sector eigenvalues  (top 8): {evals_minus[:8]}")
    if len(evals_plus) >= 2 and len(evals_minus) >= 1:
        print(f"  lambda_2^even = {evals_plus[1]:.6f}")
        print(f"  lambda_1^odd  = {evals_minus[0]:.6f}")
        print(f"  Relative error: {abs(evals_plus[1] - evals_minus[0]) / max(abs(evals_plus[1]), abs(evals_minus[0]), 1e-15):.6f}")

    # 6. Parity pairing for top-k pairs
    print("\n--- EXTENDED PARITY PAIRING (top-k pairs, sample matrix) ---")
    n_pairs = min(len(evals_plus) - 1, len(evals_minus))
    for k in range(min(n_pairs, 6)):
        lam_even = evals_plus[k + 1]  # skip top even eigenvalue (outlier)
        lam_odd = evals_minus[k]
        denom = max(abs(lam_even), abs(lam_odd), 1e-15)
        err = abs(lam_even - lam_odd) / denom
        print(f"  Pair {k}: lambda_{k+2}^even={lam_even:.6f}, lambda_{k+1}^odd={lam_odd:.6f}, "
              f"rel_err={err:.6f}")

    # 7. Overall verdict
    print("\n" + "="*70)
    print("VERDICT")
    print("="*70)
    errs = np.array(all_results[best_name])
    errs = errs[~np.isnan(errs)]
    mean_err = np.mean(errs) if len(errs) > 0 else float('nan')

    if mean_err < 0.01:
        print(f"PARITY PAIRING: STRONG MATCH (mean error {mean_err:.4f} < 1%)")
    elif mean_err < 0.05:
        print(f"PARITY PAIRING: MODERATE MATCH (mean error {mean_err:.4f} < 5%)")
    elif mean_err < 0.15:
        print(f"PARITY PAIRING: WEAK MATCH (mean error {mean_err:.4f} < 15%)")
    else:
        print(f"PARITY PAIRING: NO MATCH (mean error {mean_err:.4f} >= 15%)")

    source = "GPT-2" if USE_GPT2 else "synthetic causal softmax"
    print(f"\nSource: {source}")
    print(f"Best normalization: {best_name}")
    print(f"Total matrices tested: {len(errs)}")


if __name__ == '__main__':
    run_experiment()
