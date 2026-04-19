/*
 * Fast compatibility check for 3D convex subset transfer matrix.
 * Uses __int128 to avoid overflow in the DP accumulator.
 *
 * Compile: cc -O3 -shared -fPIC -o compat_check.so compat_check.c
 */

#include <stdint.h>

typedef __int128 int128_t;

int are_compatible(const int *L1, const int *U1,
                   const int *L2, const int *U2, int m) {
    for (int i1 = 0; i1 < m; i1++) {
        if (L1[i1] >= m) continue;
        for (int i2 = i1; i2 < m; i2++) {
            if (L2[i2] >= m) continue;
            if (L1[i1] > U2[i2]) continue;

            int col_lo = L1[i1];
            int col_hi = U2[i2];

            for (int i = i1; i <= i2; i++) {
                if (L1[i] >= m || L1[i] > col_lo || U1[i] < col_hi)
                    return 0;
                if (L2[i] >= m || L2[i] > col_lo || U2[i] < col_hi)
                    return 0;
            }
        }
    }
    return 1;
}

int have_comparable(const int *L1, const int *U1,
                    const int *L2, const int *U2, int m) {
    for (int i1 = 0; i1 < m; i1++) {
        if (L1[i1] >= m) continue;
        for (int i2 = i1; i2 < m; i2++) {
            if (L2[i2] >= m) continue;
            if (L1[i1] <= U2[i2]) return 1;
        }
    }
    return 0;
}

/*
 * Sum with __int128 accumulator.
 * dp_vals is passed as two int64 arrays (high and low parts).
 * Result returned as two int64 outputs.
 */
void sum_compatible_128(const int *L1, const int *U1,
                        const int *configs,
                        const int64_t *dp_hi, const int64_t *dp_lo,
                        int n, int m, int mode, int empty_idx,
                        int64_t *out_hi, int64_t *out_lo) {
    int128_t total = 0;
    for (int j = 0; j < n; j++) {
        if (j == empty_idx) continue;
        if (dp_hi[j] == 0 && dp_lo[j] == 0) continue;

        const int *L2 = configs + j * 2 * m;
        const int *U2 = L2 + m;

        int ok = 0;
        if (mode == 0) {
            ok = are_compatible(L1, U1, L2, U2, m);
        } else {
            ok = !have_comparable(L1, U1, L2, U2, m);
        }

        if (ok) {
            int128_t val = ((int128_t)dp_hi[j] << 64) | (uint64_t)dp_lo[j];
            total += val;
        }
    }

    *out_hi = (int64_t)(total >> 64);
    *out_lo = (int64_t)((uint64_t)total);
}

int check_one_compatible(const int *configs, int idx1, int idx2, int m) {
    const int *L1 = configs + idx1 * 2 * m;
    const int *U1 = L1 + m;
    const int *L2 = configs + idx2 * 2 * m;
    const int *U2 = L2 + m;
    return are_compatible(L1, U1, L2, U2, m);
}

int check_one_comparable(const int *configs, int idx1, int idx2, int m) {
    const int *L1 = configs + idx1 * 2 * m;
    const int *U1 = L1 + m;
    const int *L2 = configs + idx2 * 2 * m;
    const int *U2 = L2 + m;
    return have_comparable(L1, U1, L2, U2, m);
}
