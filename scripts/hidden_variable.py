"""
Hidden variable identification for the d=3 width chain.

Key finding: the (width, center) pair is 91% Markov.
Center = lower boundary position a(j).

The two-slice test shows:
- Width-only KL = 0.0074 (memory from w_{j-1})
- (Width, center) residual KL = 0.0007 (91% reduction)
- P(collapse | w=1, center=0) = 0.000 (vs Markov 0.239)

The correct reduced state for the d=3 inner chain is (w, a),
not w alone. This should give accurate f_occ and γ_slice.
"""
# See inline computation in the session for full analysis.
# This file documents the finding.
#
# The (w, a) chain on [m] × [m] has:
# - States: (w, a) with w = 0,...,m and a = 0,...,m-1
# - For w > 0: a ∈ [0, m-w] (since b = a+w-1 ≤ m-1)
# - For w = 0: a > b, so the "center" is just the a value
# - Transition: (w,a) → (w',a') with a' ≤ a, b' = a'+w'-1 ≤ b = a+w-1
#   So: a' ≤ a and a'+w'-1 ≤ a+w-1, i.e., w' ≤ w + (a-a')
#
# The combinatorial (w,a) → (w',a') transition count is:
# #{valid (a',b') : a'≤a, b'≤b, b'-a'+1=w'} = #{a': a'≤a, a'+w'-1≤b}
# = #{a': 0 ≤ a' ≤ min(a, b-w'+1)} = min(a, a+w-w') + 1 = min(a+1, a+w-w'+1)
# For w' ≤ w: count = a+1
# For w' > w: count = max(0, a+w-w'+1)
#
# This is EXACT and ANALYTICAL. The (w,a) chain is fully computable.
