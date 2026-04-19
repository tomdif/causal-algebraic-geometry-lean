"""
Fast brute force for |CC([3]^3)| using multiprocessing.
"""
from itertools import product
from multiprocessing import Pool
import time
import os

GRID_3 = list(product(range(3), repeat=3))
N = len(GRID_3)

def is_convex(S_set):
    for a in S_set:
        for b in S_set:
            if a[0] <= b[0] and a[1] <= b[1] and a[2] <= b[2]:
                for i in range(a[0], b[0]+1):
                    for j in range(a[1], b[1]+1):
                        for k in range(a[2], b[2]+1):
                            if (i,j,k) not in S_set:
                                return False
    return True

def check_chunk(args):
    start, end = args
    count = 0
    for mask in range(start, end):
        S = frozenset(GRID_3[i] for i in range(N) if mask & (1 << i))
        if is_convex(S):
            count += 1
    return count

if __name__ == '__main__':
    total = 1 << N  # 2^27
    chunk_size = total // 28  # 28 chunks over 14 cores
    chunks = [(i, min(i + chunk_size, total)) for i in range(0, total, chunk_size)]

    print(f'Brute force over {total} subsets of [3]^3, {len(chunks)} chunks, 14 workers')
    t0 = time.time()

    with Pool(14) as pool:
        results = pool.map(check_chunk, chunks)

    count = sum(results)
    dt = time.time() - t0
    print(f'|CC([3]^3)| = {count}')
    print(f'Time: {dt:.1f}s')
    print(f'Compare: TM gave 129535, earlier BF gave 114797')
