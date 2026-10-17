# Adversarial audit: full finite C_F extension with real-growth F (17 October 2026)

## New theorem and exact scope

`CFCoherentTower.finiteRealDClosedInterval_globalResponse` instantiates the already kernel-checked finite extension theorem #191 with the **canonical** integer inverse of real growth, rather than taking an externally supplied K and inverse bound.

It takes:
- A finite ordered graph G satisfying the full growth sparsity inequality on every subset.
- A finite strict d-closed inclusion `a ≤d b`.
- A literally prescribed induced embedding of a into the countable tagged birth graph with globally strictly d-closed image.
- A real function `F : ℝ → ℝ` satisfying F(0)=0, monotonicity and unboundedness.

It returns an induced embedding of the literal target b, fixing every old vertex and giving globally strictly d-closed image.

## Hostile mathematical checks

1. **Real-versus-natural growth referee.** The finite construction only evaluates F at natural cardinalities. Monotone real growth and the Archimedean property imply that `n ↦ F(n)` remains unbounded on ℕ. Without monotonicity this implication need not hold.
2. **Generalized inverse referee.** `growthInverseSize_iff` gives the exact inequality `F(m)≤2(k+1) ↔ m≤K(k)` even on plateaus. It depends on F(0)=0; the theorem retains this hypothesis explicitly. No claim of a strictly increasing F is made.
3. **Strictness referee.** This is a *strictly d-closed*, not just self-sufficient, finite extension theorem. The old source and resulting image are globally d-closed, and the response reflects nonedges.
4. **Base-label referee.** PR #191 preserves the pointwise prescribed old embedding via subtype transports and induction. Choosing the canonical K only instantiates that theorem; it never replaces the old source by an isomorphic copy.
5. **Amalgamation referee.** The finite construction assumes growth-class membership of the input G; monotonicity/unboundedness of F alone are NOT claimed to prove closure of the finite class under d-closed free amalgamation. That separate published standing hypothesis is still needed to identify the target as the Fraïssé generic.
6. **Formalization referee.** The earlier PR #185 proves a one-step real-growth specialization but is stacked on an obsolete branch. This new theorem is strictly stronger: it specializes the *full finite* response directly and will render #185 redundant only if the exact new Lean build/axiom/placeholder audit passes.
7. **Paper referee.** The paper's growth function is usually formulated on nonnegative real arguments; the Lean theorem takes a monotone function on all ℝ. One can extend the nonnegative function as F(max(x,0)), but that adaptation should be stated rather than silently identifying the domains.
8. **Limit referee.** The result does not formalize the countable uniqueness/back-and-forth theorem, the block-root recovery identity H(R(v))=C(v), or the big Ramsey theorem.

This is internal role-separated adversarial audit, not independent external referee certification.
