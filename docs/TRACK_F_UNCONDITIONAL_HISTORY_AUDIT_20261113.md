# Track F: unconditional local and tagged-history cardinalities

13 November 2026. Internal adversarial referee panel (six mathematical
challenge roles, not independent human peer reports).

The new proof combines two already separately formalized statements:
generator independence (#517) and conditional actual-fibre cardinality
(#528). It then uses the conditional dependent-history product (#529).

1. **Generator referee.** The component canonicality predicate checks
   *every* vertex of the SCC. The theorem
   `isCanonicalAtComponent_iff_generator` proves equivalence to the
   criterion at the chosen vertex; this is not an assumption.
2. **Representation referee.** `stageClosureFromTop` is, by definition,
   the induced complete closure enumeration of the assembled assignment
   after changing only the top SCC. The conversion is definitional;
   no support-only or root-only surrogate is substituted.
3. **Uniformity referee.** The resulting next-fibre count applies to
   every legal SCC ranking, every complete context, and every component,
   not only histories which are already canonical.
4. **Dependency referee.** Tagged choices carry the actual component and
   internal bijection. The product theorem counts *reachable histories*,
   using the previously certified dependent-history recursion.
5. **Scope referee.** A bijection between histories and all permitted
   *global* vertex orders is **not** yet supplied; neither a big Ramsey
   upper bound nor a recurrence theorem follows just from this count.
6. **Formal trust referee.** Require exact-head Lean compilation,
   standard-axiom inspection of both displayed endpoints, and the
   repository placeholder scan before merging this PR.

No TeX or manuscript validation markers are changed. This branch does
not repeat the finite counting proof; it composes its established lemmas.
