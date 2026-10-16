# Adversarial audit: published real growth versus integer sizes

16 October 2026

## Mathematical statement

The published C_F condition evaluates a nondecreasing unbounded
continuous real-valued F at finite vertex-set cardinalities.
The Lean finite growth predicate uses its natural-number
restriction F_nat(n)=F(n).

If F is nondecreasing on real arguments, then F_nat is monotone.
If F is unbounded above, for every threshold t choose a real x
with F(x)>t, and then choose an integer n>x. Monotonicity gives
F(n)≥F(x)>t. Hence F_nat is unbounded on natural arguments.

With F(0)=0, the exact integer generalized inverse from
PR #172 supplies the support-dependent bound
F_nat^{-1}(2(k+1)). The fully elementary numerical chain gives
|E|≤F_nat^{-1}(2(|A|+1)) for every minimal strict d-closed
extension A<_d E whose induced graph is in C_F.

Continuity is not needed in this argument. Restriction to
integer cardinalities is the only numerical operation
required by the graph predimension construction.

## Five hostile mathematical checks

1. **Archimedean lift.** Real unboundedness alone does not
immediately exhibit a natural-number witness. The proof
uses the Archimedean property of ℝ to find n>x, and
monotonicity to compare F(x) with F(n).

2. **Monotonicity direction.** A nondecreasing function
satisfies x≤n ⇒ F(x)≤F(n). The reverse implication would
invalidate transfer of unboundedness to integer arguments.

3. **Function domain.** The theorem is stated for a function
F:ℝ→ℝ, while the paper only uses nonnegative arguments.
The proof needs growth on a cofinal set of positive real
arguments; a function on the nonnegative reals can be
extended to ℝ by its value at zero without changing any
nonnegative conclusion. A fully typed nonnegative-real
version remains a possible API refinement.

4. **Exact inverse.** The size theorem uses the exact
integer inverse from PR #172, including plateaux, not
a conservative cutoff or a false strict-monotonicity
hypothesis. The bound is evaluated at cardinalities
only, so no inverse of F on all real values is required.

5. **Genericity scope.** The numerical result does not
assert that a prescribed minimal extension is realized
over its actual embedded support. It must be combined
with finite support and split graph extraction,
actual old-support transport, bounded normalization,
and the certified global named-code response.

These are five separate internal adversarial
mathematical checks rather than independent outside
referee reports. Green validation requires final
Lean compilation, standard axioms and placeholder checks.
