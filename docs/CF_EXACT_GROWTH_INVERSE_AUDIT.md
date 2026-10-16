# Adversarial audit: exact generalized inverse at integer cardinalities

16 October 2026

## Mathematical statement

Assume F:ℕ→ℝ is nondecreasing, unbounded above and F(0)=0.
For each support size k define T=2(k+1) and let N be the first
integer with F(N)>T. Then N>0, since F(0)=0≤T.

The integer generalized inverse at T is M=N−1.
Because N is the *first* strict crossing, F(M)≤T; by
monotonicity all n≤M also satisfy F(n)≤T.
Conversely, n≥N implies F(n)≥F(N)>T.
Therefore the exact equivalence holds:

  F(n)≤2(k+1)  iff  n≤M.

The bound M, not the conservative N used in the preceding
module, is precisely the largest integer allowed by the
growth inequality. Consequently the paper's
F^{←}(2(k+1)) has a canonical Lean representative.
Combining this with the finite strict-hull and every-generator
theorems yields |E|≤M for each minimal strict C_F extension
A<_d E.

## Five adversarial mathematical checks

1. **Nonempty admissible set.** F(0)=0 and T≥0 ensure the
first strict threshold crossing N is positive. Without
a point below T, N−1 could not represent a maximum
of the admissible set.

2. **Flat intervals.** The proof uses nondecreasing F,
not strictly increasing F. An arbitrarily long plateau
at value exactly T is correctly included; its last
index is N−1.

3. **Strict cut-off.** Using F(N)≥T instead of F(N)>T
would give the wrong inverse on a plateau at T.
The strict inequality is crucial and explicitly
used in the Nat.find construction.

4. **Integer versus real domain.** The actual paper
defines F on nonnegative reals. This module proves
the exact generalized inverse for its restriction to
natural cardinalities. Deriving the integer growth
hypotheses from the published continuous unbounded
real function remains a separate elementary interface.
No use of continuity is needed in the discrete theorem.

5. **Scope.** This settles the *numeric* part of the
bounded finite local catalogue, but does not by itself
show that every abstract minimal extension has been
split, transported to the literal embedded support,
and realized in the countable tagged level. The
latter uses the split graph, named-base transport
and exact global response modules.

A final green annotation requires complete Lean compilation,
standard-axiom reports, and placeholder scans. All five
roles are internal adversarial checks, not external
independent referee-agent certifications.
