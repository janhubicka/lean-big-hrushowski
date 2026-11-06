# Track A — adversarial audit of countable finite-stage recognition

Date: 1 November 2026. Scope: `C0CompleteUnaryCovers.lean` and
`C0CountableCanonicalStages.lean`; stacked on the conditional
countable recognition criterion of PR #275.

This is a role-separated adversarial review within the formalization.
No independent human or external referee agents were available.

## Mathematical simplification

Let `N` be a graph on ℕ and `C : ℕ → Finset ℕ` a set-valued unary
operation. Assume every finite subset lies in a finite stage
`stage n`. For each stage, require a *literal* minimal strong
component index `κ_n`, such that
`C(x)` is **exactly** the image of the complete canonical unary value
on that induced finite stage, not merely its intersection with it.

These finite stage hypotheses alone imply:

1. **Reflexivity**: each `x` lies in `C(x)`.
2. **Transitivity**: `y∈C(x)` implies `C(y)⊆C(x)`.
3. **Finite cover**: `⋃_{x∈s} C(x)` is a finite `C`-closed superset
   of every finite `s`, without iteration.
4. **Local strongness**: every finite `C`-closed `s⊆stage n` is
   strong inside that stage, by the finite canonical-value theorem.
5. **Global strongness**: every finite `C`-closed `s` is strong in
   `N` by cofinality of the finite stages.
6. **2-sparsity**: every finite subset has nonnegative predimension.
   Apply local strongness to the empty set in a containing stage
   and restrict its strongness to the given subset.

Therefore `N` is induced-isomorphic to `M₀` once it has the
**full labelled strong graph extension property**. That last
property is not established here or assumed in disguise.

The endpoint `graphReduct_iso_generic_of_canonicalStages_and_extension`
has precisely the cofinal-stage hypothesis, the exact finite
canonical-presentation hypothesis and the labelled graph extension
property. No separate `acl` formula, functional homogeneity,
ambient sparsity axiom, or finite closed-cover axiom is postulated.

## Referee 1 — complete values versus a truncation

The equality `C(x)=image(canonicalValue)` is crucial. A weaker
condition `C(x)∩stage n=canonicalValue` would not imply the stage is
closed under the ambient function and would not identify the
functional substructure. The proof never makes this substitution.

## Referee 2 — literal subtype transport

For a selected finite `s⊆t`, form
`S={x∈t:x∈s}` in the subtype `{x // x∈t}`. The proof identifies
`image(S, Subtype.val)=s` and `image(univ, Subtype.val)=t`
before transporting strongness. It invokes
`GraphOn.strong_image_iff`, which requires injectivity and
**induced adjacency equivalence**; both hold for the literal
stage inclusion. It never treats a mere graph homomorphism
as an induced embedding.

## Referee 3 — cofinality

The stages need not be consecutive initial segments or separately
globally strong. But *finite-subset* cofinality is required; pointwise
coverage without monotonicity is insufficient. For a test set
`b⊇s`, choose one stage containing all of `b`, not separate
stages for its vertices.

## Referee 4 — transitivity and counterexamples

For an arbitrary reflexive unary operation, finite unions of values
need not be closed. Example:
`C(0)={0,1}`, `C(1)={1,2}`, `C(2)={2}`.
The generated set of `{0}` is `{0,1}`, which is not closed.
The transitivity premise is therefore necessary for the abstract
finite-cover lemma. The actual canonical values satisfy it by
transitivity of component reachability.

Independent exhaustive computation checks all 66,067 operations on
sets of size 0–4. Exactly 390 are complete closures; their 5,931
finite generated-set cases satisfy extensivity and closedness.

## Referee 5 — sparsity

The finite minimal-component stages are built from the empty
structure, so the empty subset is strong in each stage. This yields
the ambient nonnegative predimension of every finite set by
restricting inside a containing stage. No 2-sparsity assumption is
needed in the streamlined recognition endpoint.

## Referee 6 — the remaining functional Fraïssé gap

This result does **not** construct the finite-stage sequence or
prove its functional extension property. These are the outstanding
Track A tasks. The finite two-sided functional amalgamation already
certified on main is an input to a new functional Fraïssé
construction, not a substitute for one.

To establish the missing labelled *graph* extension property of
the functional limit, take a finite strong graph base `A`, first
close it under `C` to get `S`, freely amalgamate the graphs of
`S` and the finite target graph over **A**, apply
`FiniteSpan.exists_canonical_functional_strong_amalgam`,
and use the countable functional extension property over `S`.
The resulting induced target copy must have globally strong image.
A strong graph set is not necessarily functionally closed.

The existing conditional PR #275 and the new finite-stage
normalization do not yet verify that extension argument or
construct the functional countable limit. No manuscript marker for
`prop:C0-free-generic` should be promoted on their basis.

## Certification gate

A pass requires an exact Lean build, all new
`#print axioms` endpoints with only standard logical axioms,
the no-placeholder scan, and the finite regressions. The
finite Python checks are diagnostic evidence only.


## Additional adversarial panel — functional-to-strong transfer

The further modules `C0CountableFunctionalStrongImages.lean` and
`C0CountableStageFunctionalExtension.lean` reduce countable graph
genericity to a specific **functional** extension property over
cofinal canonical stages. This is the remaining finite-to-countable
bridge; existence of the functional limit is still not asserted.

**Referee 7 — nonclosed strong base.** A graph-strong substructure
need not be closed under `C`. For example, a later endpoint of a
two-vertex edge can be strong in the graph, while its complete unary
value includes the earlier endpoint. Hence the labelled graph map
is embedded into a sufficiently large *closed finite stage*
before performing the graph free amalgam. The strong span is glued
over the original graph base, never treated as a functional base.

**Referee 8 — genuine source map.** The finite tagged graph-span
theorem gives induced maps `f` and `g` identifying *only* the
prescribed graph base. The source map into the countable graph is
retained literally: the functional realization fixes every
vertex of the old stage, and therefore every source vertex.
No replacement by an abstract isomorphic copy is allowed.

**Referee 9 — inducedness.** Every graph embedding used in the
transfer is an `↔` on adjacency, not just an implication.
An omitted nonedge would invalidate predimension invariance and
the strong-image transfer.

**Referee 10 — complete unary values.** The functional realization
condition is equality of the full `C`-value for **every** new
vertex, including the entire finite image of its canonical
one-generated closure. This implies the finite realized image
is `C`-closed, hence globally strong. The image of the requested
strong target is then globally strong by composition of strong
embeddings. Restricting an induced graph map alone would not
justify global strength.

**Referee 11 — countable hypothesis.** The only new substantive
assumption is `HasCanonicalStageExtensionProperty`, requiring
functional realization of every permitted finite canonical
extension over a literal finite canonical stage. This is a
proper functional Fraïssé extension property; it is not
`HasStrongExtensionProperty` renamed. The theorem proves the
latter from the former using the finite tagged graph-to-functional
span lift.

**Referee 12 — remaining existence.** Neither these new theorems
nor the countable recognition criterion build the functional
Fraïssé limit or prove the stage functional extension property
for a concrete recursively constructed structure. A separate
fair finite functional request catalogue is developed in
draft PR #286; the one-step response and coherent countable
functional-stage recursion remain open.

The new endpoints are registered in `CheckC0Countable.lean`
and have dedicated CI in
`.github/workflows/track-a-countable.yml`.
The main global import and axiom files are deliberately not
edited in this branch, avoiding conflicts with concurrent
`C_F` tracks. Do not mark any endpoint green without the
exact branch build and axiom audit passing.
