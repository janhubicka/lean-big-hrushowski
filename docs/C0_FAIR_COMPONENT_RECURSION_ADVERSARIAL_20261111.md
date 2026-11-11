# Track A — fair intrinsic-component recursion: adversarial audit

11 November 2026. These are seven independent *review roles applied to the argument*, not reports from external referees. Exact-head Lean build and axiom-check status must be recorded separately.

## Proposed result

On ℕ with a finite-valued reflexive/transitive complete unary operation C, repeatedly select the least numeric label x outside the current finite prefix Q for which L(x)=C(x)\\P(x)⊆Q. Adjoin all of P(x), not just x.

The resulting finite sets Q_n are nested and strictly increase. Every x belongs to some Q_n. With exact cofinal canonical C₀ stages, Q_n is C-closed, each Q_n⊂Q_(n+1) is a minimal strong step, and Q_(n+1) is globally strong. No internal component ordering is selected.

## Adversarial referees

1. **Fairness versus rank.** Minimize closure cardinality only to show that an enabled component exists. The actual recursion minimizes numerical label. Otherwise infinitely many minimal-rank components could starve a larger-rank component.
2. **Finite lower dependencies.** For y∈L(x), C(y) is a strict subset of C(x), giving cardinal descent. No descent is claimed within P(x). Finiteness of C(x) is essential.
3. **Persistence of eligibility.** If L(x)⊆Q_n, the same inclusion holds in every later prefix. If x remains outside Q, it stays eligible, so the chosen label must be ≤x.
4. **No starvation.** While x is enabled but unlisted, each step consumes a previously unlisted label y≤x. There are only x+1 such labels. The proof counts intersection with the *fixed finite* range {0,…,x}, not the (possibly infinite) lower-rank strata.
5. **Whole-component step.** New vertices are precisely the equality class P(x) of full unary values, so no selected component can overlap a previously closed prefix. The selected generator is not privileged inside its component.
6. **Graph-theoretic dependence.** Pure unary fairness alone gives no graph strength. The minimal-strong and global-strong assertions explicitly invoke the previously certified canonical-stage one-component theorem and closed-set strongness.
7. **Formal trust and manuscript scope.** The ten named endpoints require exact-head kernel and standard-axiom checks and a placeholder scan. Until the new workflow passes, this is an unverified proof candidate. Even once certified it does not establish a uniform within-component ordered representative, complete canonical unary-value recovery from the resulting *chosen* vertex enumeration, or full functional homogeneity; do not change the manuscript's PARTIAL marker on these grounds alone.

## Potential counterexamples to watch

- Countably many rank-one singleton classes and one rank-two class: global rank sorting does **not** exhaust at finite times. Least-enabled-label recursion does.
- A component with two vertices and the same full C-value: selecting only one vertex is not a minimal-component step.
- A finite prefix not C-closed: a previously selected same-class vertex can overlap the next class, invalidating the graph step.
- Nontransitive or nonreflexive finite-valued unary data: strict cardinal descent and the component partition can fail.
