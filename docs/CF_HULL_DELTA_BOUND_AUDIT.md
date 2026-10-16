# Adversarial audit: predimension of a finite strict d-closed hull

16 October 2026

## The short argument

Let A⊆C be finite. Consider all intermediate vertex sets
Y, A⊆Y⊆C, satisfying δ(Y)≤δ(A). The family is finite and
nonempty (A itself is a member). Choose a member Y of
*maximum cardinality*.

If Y⊂Z⊆C and δ(Z)≤δ(Y), then δ(Z)≤δ(A), so Z is another
member of the same family and has larger cardinality.
This contradicts the choice of Y. Therefore

    Y ≤d C,       δ(Y) ≤ δ(A).

Let H=cl_C^d(A) be the least strictly d-closed subset
containing A. The already verified finite hull theorem
gives H≤d C and H⊆Y. By restriction H≤d Y.
Consequently δ(H)≤δ(Y)≤δ(A).

This establishes the exact interface needed for the
published C_F closure-size bound, but without a second
recursive closure or a predimension-minimization argument.

## Five separate hostile mathematical checks

**1. Ties are essential.** Minimizing δ alone does not
guarantee strict closure when a larger set has the
same predimension. Choosing a *maximal cardinality*
candidate automatically excludes ties and yields the
required strict inequality.

**2. No hidden assumption on the candidate family.**
A belongs to the family provided A⊆C. Every member is
a subset of finite C, so a largest cardinality is
attained. No lower boundedness or monotonicity of δ
is needed for the maximal-cardinality step.

**3. Least versus arbitrary closed superset.** The fact
that Y≤d C and δ(Y)≤δ(A) does not by itself imply that
an arbitrary closed set has small predimension.
The proof specifically takes the *least* hull H
and uses H⊆Y and strict closure restricted to Y.

**4. Submodularity boundary.** The first existence
statement works for any finite integer predimension.
The second invokes the previously certified theorem
that intersections of d-closed subsets are d-closed.
That theorem uses the submodularity stored in
Predimension; we do not silently drop this hypothesis.

**5. C_F consequence and limitation.** Applied to
the hull of P∪{x} in a minimal strict d-closed
extension, the lemma gives δ(E)≤δ(P∪{x})≤2(|P|+1).
Together with the actual growth inequality on E,
this implies F(|E|)≤2(|P|+1). To turn this inequality
into |E|≤K(|P|), one still must use a stated
eventual-growth/inverse-bound property of F.
No numerical bound is smuggled into this abstract
predimension theorem.

The exact Lean lemmas must pass final integrated build,
standard-axiom checks and placeholder scan before
receiving green validation markers. The five reviews
above are independent internal adversarial mathematical
passes, not external referee-agent certificates.
