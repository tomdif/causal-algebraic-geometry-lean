/-
  BlockThreshold.lean — The contiguous block threshold theorem.

  THEOREM: Θ(L, d, m) = (d + L + 1) · m − d

  For a contiguous block of L violations at positions {d,...,d+L-1},
  with depth constraint 2d + L ≤ m.

  Generalizes DepthThreshold (L = 1 case).
  Verified computationally at m = 8, 10, 12, all L and d.

  PROOF STATUS: 1 sorry. The tail+head bound approach from DepthThreshold
  is insufficient for L ≥ 2. The proof requires Finset sum-splitting into
  three regions (left/block/right), bounding each region separately.
-/
import CausalAlgebraicGeometry.DepthThreshold

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

namespace CausalAlgebraicGeometry.BlockThreshold

open CausalAlgebraicGeometry.DepthThreshold

noncomputable section
open scoped Classical

/-- The contiguous block threshold theorem.
    For violations at positions d, d+1, ..., d+L-1:
      Σ(a+b) ≥ 2m + (d+L-1)(m-1).
    Equivalently: Σ(a+b) ≥ (d+L+1)m - d.

    PROOF APPROACH: Split sum into three regions:
    - Left {x < d}: each b(x) ≥ b(d) ≥ m+1-a(d). Contrib ≥ d·b(d).
    - Block {d ≤ x ≤ d+L-1}: each a(x)+b(x) ≥ m+1. Contrib ≥ L·(m+1).
    - Right {x > d+L-1}: each a(x) ≥ a(d+L-1). Contrib ≥ (m-d-L)·a(d+L-1).
    Total ≥ d·b(d) + L(m+1) + (m-d-L)·a(d+L-1).
    At the minimum (a(d)=a(d+L-1)=1, b(d)=m): this equals (d+L+1)m - d. -/
-- block_threshold: REMOVED (dead code, was sorry).
-- Statement: for L contiguous violations at positions d..d+L-1,
--   Σ(a+b) ≥ 2m + (d+L-1)(m-1).
-- Proof requires: Finset sum-splitting into left/block/right regions
-- with monotonicity bounds. The arithmetic is straightforward but the
-- Finset manipulation is ~60 lines.

end
end CausalAlgebraicGeometry.BlockThreshold
