# Track A: countable reduct criterion — adversarial audit (1 November 2026)

This review concerns the conditional theorem
`FiniteC0.graphReduct_iso_generic_of_unaryPresentation`.
It is **not** a proof that the actual functional Fraïssé limit exists,
nor that its graph reduct has the strong extension property.
The roles below are separate hostile mathematical checks by the
assistant, not independent external referees.

## Exact theorem interfaces

Let `N` be a graph on ℕ, let `C : ℕ → Finset ℕ` be the *full*
unary set-valued operation of a proposed C₀ presentation, and let
`stage n` be finite carrier sets covering **every finite** subset of ℕ.
Assume:

1. `N` is 2-sparse on every finite vertex set;
2. if a finite `s` is contained in `stage n` and is closed under
   the *complete* unary operation `C`, then `s` is strong in
   the induced graph on `stage n`;
3. every finite set is contained in a finite `C`-closed set; and
4. `N` has the full **labelled strong graph extension property**
   for arbitrary finite strong graph diagrams.

Conclusion: `N` is induced-isomorphic to the already certified
countable strong generic `M₀`.

The proof first derives global strongness of every finite `C`-closed
set: for a finite test extension `b ⊇ s`, choose a stage containing
`b` and restrict relative strongness from this stage to `b`.
This requires **neither** global strongness of the stage nor a
particular monotone or gap-free stage numbering. Then every finite
set is in a globally strong `C`-closed container, and the existing
`genericTwoSparseGraph_unique` theorem applies.

## Adversarial roles

**Cofinality referee.** Merely covering each vertex separately by a
finite stage is insufficient unless the stages are monotone or finite
subset coverage is separately proved. The theorem explicitly assumes
coverage of *every finite test set*. No arbitrary infinite test set is
introduced into predimension.

**Closure referee.** `C` is the complete vertex-valued unary
operation, not an approximation that records only old neighbours.
The theorem applies only to sets closed under this entire value.
A graph-strong set need not be unary-closed.

**Strongness referee.** The local hypothesis is `IsStrong s (stage n)`
for every stage containing `s`. The proof does not silently infer
strongness of `s` in an *unrelated* finite container or assume that
the stage itself is globally strong.

**Genericity referee.** The labelled strong extension property is an
independent premise. Without it the conclusion is false; for example,
the countably infinite edgeless graph is 2-sparse, has finite strong
covers and locally finite identity closure but is not the sparse
strong Fraïssé generic. This rules out an attempted shortcut from
finite closure and age heredity alone.

**Back-and-forth referee.** The only countable identification step
is an invocation of the previously verified
`FiniteCatalogue.genericTwoSparseGraph_unique`, whose exact three
hypotheses (sparsity, finite strong covers, labelled extension
property) are supplied. No unproved functional homogeneity theorem
or model-theoretic algebraic closure identification is used.

**Scope referee.** To instantiate the result for the intended
functional limit one must still construct a concrete countable
structure with finite closed covers, establish all finite-stage
closed-set strongness via the canonical presentation, and prove
the *full* labelled strong graph extension property using the finite
graph-span functional lift and the extension property of the actual
functional limit. None is smuggled into the conclusion.

## Next Track A mathematical obligations

- Fully certify the finite two-sided functional amalgamation theorem
  in stacked PR #274, *after* PR #271.
- Construct the countable functional Fraïssé limit, or supply an
  explicitly equivalent construction, with finite complete unary
  closed covers and genuine functional extension property.
- Derive the local closed-set strongness condition at **every**
  induced finite presentation stage.
- For an arbitrary finite **strong graph** base `A`, take its finite
  unary closure `C`, form the finite strong graph amalgam of `C`
  and the prescribed target graph over `A`, and lift that graph
  span to a functional extension preserving `C` exactly. Then
  apply the functional extension property and restrict back to the
  graph target. The distinction between a strong graph base and
  a unary-closed functional base is essential.
- Instantiate this criterion, and only then upgrade the
  manuscript's `prop:C0-free-generic` marker.

## Certification gate

A successful Lean build + exact `#print axioms` for the four new
declarations, placeholder scan, and integrated finite regressions
are required before any certificate is claimed. Internal adverse
checks above do not replace these. Keep this as a separate PR so it
does not block finite Track A proof development.
