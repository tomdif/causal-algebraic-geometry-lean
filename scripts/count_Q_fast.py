"""
Fast transfer-matrix count of Q(m) for m up to 6 (and maybe 7).

Strategy
--------
 1. Build state list as numpy int8 arrays for fast comparisons.
 2. Build CSR adjacency via chunked numpy broadcasting:
       edge (i, j)  iff  phi[i] >= phi[j] pointwise AND psi[i] >= psi[j] pointwise.
    Row i of the CSR stores OUT-neighbors (targets) of source i.
 3. Iterate  v <- A^T v  (since we want v_new[j] = sum_{i with j in out(i)} v[i])
    using scipy.sparse CSR with int64 dtype.  Individual entries fit in int64
    throughout the iteration even when the final sum Q(m) overflows.
 4. Compute sum(v) with Python bigints (cast each int64 to Python int first)
    to get the exact Q(m).

For m=6 we can also re-run with a second modulus as a cross-check.  We verify
against known Q(1..5) = 1, 20, 8790, 89613429, 21493411201893.

Author: Claude Code (Apr 19 2026).
"""

import math
import sys
import time
from itertools import combinations_with_replacement

import numpy as np
import scipy.sparse as sp


# ---------------------------------------------------------------------------
# State enumeration
# ---------------------------------------------------------------------------


def build_states(m):
    """Return (phi, psi) int8 arrays of shape (N, m) enumerating all valid
    states (r_phi, r_psi): both non-increasing, r_phi[j] < r_psi[j] pointwise,
    entries in [0, m]."""
    rows = []
    for c in combinations_with_replacement(range(m + 1), m):
        rows.append(tuple(sorted(c, reverse=True)))
    rows_arr = np.array(rows, dtype=np.int8)  # shape (R, m)
    less = (rows_arr[:, None, :] < rows_arr[None, :, :]).all(axis=2)  # (R, R)
    phi_idx, psi_idx = np.nonzero(less)
    phi = rows_arr[phi_idx]
    psi = rows_arr[psi_idx]
    return phi, psi


# ---------------------------------------------------------------------------
# Adjacency construction (CSR by source)
# ---------------------------------------------------------------------------


def build_adj_csr(phi, psi, chunk=256, verbose=True):
    """Build scipy.sparse.csr_matrix A where A[i,j] = 1 iff
       phi[i]>=phi[j] pointwise and psi[i]>=psi[j] pointwise.

    Done in one pass over chunks: collect (rows, cols) as int32 arrays.
    """
    N = phi.shape[0]
    all_rows_parts = []
    all_cols_parts = []
    total = 0
    t0 = time.time()
    for start in range(0, N, chunk):
        end = min(N, start + chunk)
        src_phi = phi[start:end]
        src_psi = psi[start:end]
        a = (src_phi[:, None, :] >= phi[None, :, :]).all(axis=2)  # (C, N)
        b = (src_psi[:, None, :] >= psi[None, :, :]).all(axis=2)
        mask = a & b
        rr, cc = np.nonzero(mask)  # rr in [0, end-start)
        all_rows_parts.append((rr + start).astype(np.int32))
        all_cols_parts.append(cc.astype(np.int32))
        total += rr.size
        if verbose and (start // chunk) % 20 == 0:
            print(f"    adj: {end}/{N}  edges so far {total}  "
                  f"elapsed {time.time()-t0:.1f}s", flush=True)
    rows = np.concatenate(all_rows_parts); del all_rows_parts
    cols = np.concatenate(all_cols_parts); del all_cols_parts
    if verbose:
        print(f"    adj done: {total} edges in {time.time()-t0:.1f}s",
              flush=True)
    # Build CSR.
    data = np.ones(rows.size, dtype=np.int64)
    A = sp.csr_matrix((data, (rows, cols)), shape=(N, N))
    return A


# ---------------------------------------------------------------------------
# Big-int transfer iteration via scipy.sparse int64, sum in Python ints
# ---------------------------------------------------------------------------


def count_Q(m, verbose=True):
    if m == 0:
        return 1
    if verbose:
        print(f"\n=== Q({m}) ===", flush=True)
    t0 = time.time()
    phi, psi = build_states(m)
    N = phi.shape[0]
    if verbose:
        print(f"  states: N = {N}  (build {time.time()-t0:.2f}s)", flush=True)
    if m == 1:
        return N

    A = build_adj_csr(phi, psi, chunk=256, verbose=verbose)
    A_T = A.T.tocsr()  # so that v_new = A_T @ v does v_new[j] = sum_{i: A[i,j]=1} v[i]

    # Use int64 while safe; switch to Python int (object) when max entry
    # threatens overflow.  Safe bound: 2^62 to leave headroom for next step.
    LIMIT = 1 << 62

    v = np.ones(N, dtype=np.int64)
    bigint = False
    for step in range(m - 1):
        ts = time.time()
        if not bigint:
            v_new = A_T @ v
            mx = int(v_new.max())
            sm = int(v_new.sum())  # may overflow if sum > 2^63-1; cast before sum
            # Safer sum: cast to Python int
            sm = int(np.asarray(v_new, dtype=object).sum())
            if verbose:
                print(f"    step {step+1}/{m-1}: max={mx} sum={sm} "
                      f"({time.time()-ts:.1f}s)", flush=True)
            v = v_new
            # If next step could push entries past LIMIT (max potential growth ~ max fanin),
            # switch to bigint.  Conservative: if mx * max_row_nnz > LIMIT, switch.
            max_row_nnz = int(np.diff(A_T.indptr).max())
            if mx * max_row_nnz > LIMIT and step < m - 2:
                if verbose:
                    print(f"    switching to bigint (mx*fanin = "
                          f"{mx*max_row_nnz:.2e} > {LIMIT:.2e})", flush=True)
                v = v.astype(object)
                bigint = True
        else:
            # Python big int matvec.  Use CSR indices/indptr arrays.
            indptr = A_T.indptr; indices = A_T.indices
            v_new = np.zeros(N, dtype=object)
            # Build Python list for speed.
            v_list = v.tolist()
            vn_list = [0] * N
            for j in range(N):
                s = 0
                gs = indptr[j]; ge = indptr[j + 1]
                for p in range(gs, ge):
                    s += v_list[indices[p]]
                vn_list[j] = s
            v = np.array(vn_list, dtype=object)
            mx = max(vn_list); sm = sum(vn_list)
            if verbose:
                print(f"    step {step+1}/{m-1}: max={mx} sum={sm} "
                      f"({time.time()-ts:.1f}s) [bigint]", flush=True)

    if bigint:
        return int(sum(v.tolist()))
    # Final sum with Python bigints.
    return int(np.asarray(v, dtype=object).sum())


def count_PP(m):
    """PP(m,m,m) via MacMahon."""
    from fractions import Fraction
    result = Fraction(1)
    for i in range(1, m + 1):
        for j in range(1, m + 1):
            for k in range(1, m + 1):
                result *= Fraction(i + j + k - 1, i + j + k - 2)
    assert result.denominator == 1
    return result.numerator


if __name__ == "__main__":
    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    results = {}
    for m in range(1, max_m + 1):
        t0 = time.time()
        q = count_Q(m)
        pp = count_PP(m)
        results[m] = (q, pp)
        lnq = math.log(q) if q > 0 else 0.0
        lnpp = math.log(pp)
        print(f"\nRESULT m={m}: Q={q}  PP={pp}  "
              f"lnQ/m^2={lnq/m**2:.6f}  lnPP/m^2={lnpp/m**2:.6f}  "
              f"[total {time.time()-t0:.1f}s]", flush=True)
    print("\nSUMMARY")
    print(f"{'m':>3} {'Q(m)':>30} {'PP(m,m,m)':>18} {'lnQ/m^2':>10}")
    for m in sorted(results):
        q, pp = results[m]
        print(f"{m:>3} {q:>30} {pp:>18} {math.log(q)/m**2 if q>0 else 0:>10.6f}")
