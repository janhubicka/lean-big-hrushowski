# Adversarial audit: canonical size cutoff from monotone unbounded F

16 October 2026

## Mathematical statement

Let F: ℕ→ℝ be monotone nondecreasing and unbounded above.
For each finite support size k, choose the least integer
N=K(k) such that F(N)>2(k+1). Existence is exactly
integer-unboundedness.

If F(n)≤2(k+1), then n<N; otherwise monotonicity would
give F(N)≤F(n)≤2(k+1), contradicting the choice of N.
In particular n≤K(k), which is the numerical inverse
property assumed in the finite minimal-extension theorem.

Together with the already proposed strict-hull inequality
and minimal-growth bound, this makes

   |E| ≤ K(|A|)

for every minimal strict d-closed growth-class extension
A<_d E, without postulating an arbitrary extra inverse
parameter. The first strict index is a conservative upper
bound, slightly larger than the maximum admissible
integer cardinality if one exists.

## Five adversarial referee passes

1. **Flat intervals.** No strict monotonicity of F is needed.
A flat interval below the threshold is harmless because the
first *strict* threshold crossing occurs after all its
indices, and nondecreasing F prevents later returns.

2. **Unboundedness.** Monotonicity alone does not suffice.
If F stays bounded below 2(k+1) the first crossing does
not exist. The construction supplies a proof of existence
for each k directly from hUnbounded.

3. **Correct inequality direction.** If n≥K(k), then
F(K(k))≤F(n), contradicting F(n)≤2(k+1).
The theorem actually proves n<K(k), stronger than the
conservative n≤K(k) needed by the finite catalogue.
There is no off-by-one omission.

4. **Integer versus real function.** The paper's original
F is continuous, nondecreasing and unbounded on the
nonnegative reals. This lemma works for its restriction
to integers, with monotonicity and unboundedness of that
restriction explicit. A separate, elementary transfer
from real to integer arguments is required before
claiming the complete analytic assumptions have been
formalized.

5. **No genericity claim.** The growth-size cutoff makes
the finite catalogue large enough for minimal *growth-class*
local extensions. It does not by itself transfer an
arbitrary minimal extension over a fixed embedding to a
named local code, establish the global finite extension
property, or verify the partial functions R and H.

The exact Lean declarations are provisional until final
integrated CI, standard-axiom and no-placeholder audits.
The five roles are intentionally separated internal hostile
proof reviews, not external human referee reports.
