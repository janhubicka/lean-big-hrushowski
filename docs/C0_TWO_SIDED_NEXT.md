# Next C0 theorem: two-sided functional amalgamation

**Status: OPEN.** The graph part, closed-base frontloading,
minimal-step no-cross lemma and abstract complete-value transport
are verified. The joint application to both actual functional
factors is not yet formalised.

## Target

For two finite canonical C0 presentations (G,kappa) and (H,eta)
with a common induced finite graph P, whose complete named unary
closures agree on P and stay inside P, construct a tagged free
graph amalgam K and a canonical component indexing theta so that:

1. Both graph embeddings are induced and strong.
2. Every nonempty theta stage is a minimal strong extension.
3. All complete unary values on G transport **exactly** by
   the first embedding, with full block images.
4. All complete unary values on H transport **exactly** by
   the second embedding, with full block images.

Do not require the orders induced by kappa and eta on P to agree.

## Proof interface

* Keep kappa on the entire first factor **unchanged**.
* Apply FiniteC0.frontloadIndex_minimal_steps and
  FiniteC0.canonicalValue_frontload_eq to P in the second factor.
* Append its nonempty components outside P with fresh indices
  strictly above every first-factor index.
* Use GraphOn.minimalStrongStep_enlarged_of_local at each step.
  Its no-cross condition concerns edges between the new block
  and the first-factor tail outside P.
* Existing first-factor vertices have no new backwards paths.
  Paths from a new second-factor component may enter P but
  cannot then leave P. Values on P were assumed equal.
  Discharge the actual component-map and dependency hypotheses
  before applying TaggedAmalgam.freeDependency_wholeClosure_left
  and TaggedAmalgam.freeDependency_wholeClosure_right (or derive
  the path identity directly).

This removes the obligation to align or reorder the FIRST
witness. It is stronger and simpler than the P-first construction.

## Audits

scripts/check_c0_explicit_amalgam.py checks 8,459 finite
closed-base diagrams, verifying that the entire original left
index tuple is unchanged. It also checks a seven-vertex example
with an interleaved base and a nonsingleton triangle component.

The detailed mathematical audit is in the manuscript repository,
verification/2026-10-15_c0_left_fixed_audit.md.

These tests are not a Lean proof of the full amalgamation theorem.
The countable functional Fraïssé/reduct step is a separate obligation.
