# Adversarial audit: numerical bound for minimal strict C_F extensions

16 October 2026

## Exact reduction

For finite graph predimension δ(S)=2|S|-|E(S)|, we have δ(S)≤2|S|.

The independent strict-hull lemma (PR #168) proves
δ(cl_C^d(S))≤δ(S) for any finite ambient C.
If C belongs to the exact growth class C_F, then

  F(|cl_C^d(S)|) ≤ δ(cl_C^d(S)) ≤ δ(S) ≤ 2|S|.

In a minimal strict d-closed extension A<_d E,
every x∈E\A generates E over A. Taking S=A∪{x} gives

  F(|E|) ≤ 2(|A|+1).

Thus any K satisfying
  F(n) ≤ 2(k+1) ⇒ n ≤ K(k)
bounds the *entire extension* |E| and hence its fresh block.

The mathematical result is the exact bridge between the published
uniform finite closure bound and the actual stage-catalogue parameter.
The numerical inverse property itself remains an explicit input:
continuity, monotonicity and unboundedness of the published F are not
silently formalized by this module.

## Five adversarial mathematical checks

1. **Strictness and generators.** The claim that any fresh x
generates E over A needs the verified IsMinimalDClosedStep theorem.
It is false for arbitrary nonminimal strict d-closed extensions.

2. **Closure predimension.** The inequality δ(cl_C^d S)≤δ(S)
requires *least* strict d-closed hull, not an arbitrary extension
with strongness alone. PR #168 uses a maximum-cardinality
low-predimension superset to prove it.

3. **Missing edges.** The graph bound δ(S)≤2|S| uses the
nonnegative number of unordered edges in the induced finite set.
No assumption that δ is nonnegative is made.

4. **Real/integer interface.** The growth predicate F n≤δ(X)
is real-valued while δ is integer-valued. The proof converts the
single integer inequality δ(H)≤2|S| into its real form; it must
not conflate a cardinality lower bound with an integer predimension.

5. **Correct use of the inverse.** A property
F(n)≤2(k+1)⇒n≤K(k) must be supplied. Monotonicity of F by itself
is insufficient if F remains bounded. The inverse hypothesis is
satisfied by the manuscript's generalized inverse under its
unbounded-growth assumptions, but the analytic connection is
not yet declared GREEN by this PR.

## Scope

The lemma bounds cardinalities of minimal extensions and fresh blocks,
conditional on a numerical inverse bound. It does not show that an
arbitrary minimal extension is a member of the relevant growth class:
that must be provided separately, nor does it construct the actual
named local request or prove genericity. Together with certified
split-graph extraction (#167), named-base transport (#165), and bounded
normalization (#166), it supplies the remaining numeric input to the
eventual genericity proof.

All five roles are separated internal adversarial proof-obligation
checks, not independent outside referees. Final CI must check the
Lean declarations, standard axioms, and absence of placeholders.
