# Countable C₀ closure-component enumeration: English proof plan

Date: 8 November 2026; status updated 13 November 2026.
This proof plan is **not** a separate Lean certificate. It isolates the remaining enumeration argument in
`prop:C0-free-generic` after the countable functional limit's
cofinal-stage extension property and graph-reduct identification
have been certified.

## Statement to formalize

Let `N` be the countable graph reduct of a countable functional
C₀ structure with complete one-generated unary closures
`C:ℕ→Finset ℕ`. Assume it has cofinal finite canonical C₀
presentations, with *exact* complete unary values on the finite
stages. We wish to enumerate the vertices by consecutive **finite
intrinsic components**, in such an order that all earlier
components needed by a component precede it. At every component
cut the graph prefix is globally strong, and each nonempty
increment is minimal strong.

The order of the components must have type ω, not merely be a
well-order, and each vertex's canonical unary value in the
enumeration must equal its original full value C(x).

## 1. Intrinsic finite classes

For x, put

```text
P(x) = {y : C(y) = C(x)}.
L(x) = C(x) \ P(x).
```

Every member of P(x) belongs to C(x), so P(x) is finite and
nonempty. These sets are disjoint or equal and partition ℕ.
If y belongs to L(x), then C(y) is a **proper subset** of C(x),
so |C(y)| < |C(x)|. The entire class P(y) lies in L(x).
Thus each component has only finitely many strict lower
components and the lower-component relation has no cycles.

The merged Lean module
`C0CountableIntrinsicComponents.lean` proves these
elementary facts, together with identification of P(x)
with the component-index fibre in every finite canonical
presentation. This last fact uses the already validated
`canonicalValue_eq_iff_index_eq`.

## 2. Fair enabled-component algorithm

Give each component P its priority

```text
priority(P) = min P.
```

These priorities are distinct natural numbers.

Starting from the empty union, at step i choose the unlisted
component with **smallest priority among those whose strict
lower components have all already been listed**.
This set of enabled components is nonempty: among the unlisted
components, choose one with smallest |C(x)|. If it had an
unlisted lower component, that component would have strictly
smaller closure size, a contradiction.

Every component is eventually chosen. Use induction on its
closure size. All its finitely many lower components have
smaller sizes and hence are eventually chosen. The component
then remains enabled. If it is not selected, the rule must
select some previously unlisted component of smaller priority.
Only finitely many components have smaller priority, and none
can be selected twice. Therefore the fixed component is
chosen after finitely many further steps.

There are infinitely many components, since ℕ is infinite
and every component is finite. The selected component order
therefore has type ω. Each component is a finite nonempty set,
so concatenating finite orders on the selected components
gives a vertex enumeration of type ω, with components as intervals.

**Incorrect shortcut:** sorting components globally by
|C(x)| is not valid. There may be infinitely many
minimal-closure components, which would postpone every
component of larger closure size beyond all natural steps.
The fair enabled-minimum algorithm is essential.

## 3. Closed and minimal strong cuts

Let Q be the union of the previously chosen components,
and P the next component. Q is finite and C-closed by
induction. Indeed, for any x in a previously chosen
component, C(x) consists of its own component and its
strict lower components, all already listed.

The set Z = Q ∪ P is also finite and C-closed, because all
strict lower components of P precede P.

Choose a finite canonical stage containing Z.
By the certified finite closed-heredity theorem,
the induced functional structure on Z has a canonical
minimal-component presentation and the *same* full unary
values. Its component fibres are intrinsically P(x), so
Z\Q consists of exactly the single component P.

Apply the certified finite closed-base frontloading theorem
to Q inside this finite presentation. Its complete values
and minimal-step property are preserved, Q is frontloaded,
and the only nonempty component remaining is P. Hence
Q ≤ Z is a **minimal strong extension**.
Since Z is C-closed, the certified countable closed-set
strongness theorem makes Z globally strong in N.
Thus the whole enumerated sequence consists of finite
globally strong prefixes and nonempty minimal strong increments.

The finite interval result (`closed_one_component_interval_minimal`,
PR #385) and its countable transfer
(`canonicalStages_oneComponentInterval_minimal`, PR #394) now certify
this one-component step independently of a global enumeration.
The **fair recursive finite prefixes and their exhaustion** were
kernel-certified and merged in PR #412. PR #417 subsequently certified
each vertex's unique component birth, the exact fresh component, and
inclusion of its entire complete unary value in the birth prefix.
The fair prefixes have since been certified as cofinal canonical finite
presentations (#433). The lexicographic order of vertices, with any
componentwise injective local numbering, has also been shown to have
order type ω (#439, #457). What remains for the paper's ordered
expansion is the **uniform choice of ordered representative inside
each component**, not another construction of the component order.

The intrinsic finite-class lemma alone does not justify this
step. The hereditary and frontloading theorems are needed.

## 4. The unary operation is unchanged

For any vertex x, its full value C(x) is contained in
the finite prefix ending with the component P(x), and
the induced finite presentation on that prefix has
exactly the inherited complete canonical value C(x).
The exact equality of the full canonical value for the fair birth
index was established in the Lean-certified PRs #419, #422 and #427.
Thus the fair *component chronology* recovers C(x), with no hypothesis
that the component order is the original finite-stage order.

No generator is singled out within a component.
For the *additional closure-respecting ordered expansion*
in the manuscript, the finite order **inside** each
component must be selected by a fixed representative of
its ordered one-generated closure type over the already
ordered lower components. Ordering every block by
numerical vertex labels alone need not satisfy the
uniform representative convention.

## 5. Functional extension, universality and homogeneity

The countable functional-stage extension property and identification
of the graph reduct with M₀ were kernel-certified and merged in
PR #375. The constructed limit has finite closed covers, and each
finite canonical stage has the correct complete unary values.

The *arbitrary closed-base* extension property is now proved, not
postulated. The proof first chooses a finite canonical stage S
containing the given finite C-closed base A. It then forms the
two-sided functional free amalgam of S and the requested finite
extension B over A, preserving **both** complete unary functions.
The finite amalgam is realized over S by the stage extension
property, giving an embedding of B which fixes A pointwise.
The constituent finite two-sided amalgamation (#451), named-base
response (#453), complete named values (#454), and full theorem
(#459) have all passed their exact-head Lean and source audits
and merged.

The actual functional back-and-forth limit is certified in #456.
The closed functional joint-step construction and the extension
of each finite closed functional partial automorphism to a
global automorphism were certified on a clean branch and merged
in #512. This is **functional homogeneity**, not merely a graph
reduct isomorphism. A final corollary stated directly for any
isomorphism of arbitrary finite C-closed subsets (without separate
strongness certificates) is in clean draft #522; its original
stacked theorem passed Lean on #495, while the new integration
head requires fresh checks. A separate finite functional age
universality corollary from the empty closed base is in draft #511,
also awaiting exact-head certification.

These statements concern the **unordered functional C₀ limit**.
They do not choose a local ordered representative within each
intrinsic component, nor do they establish the ordered expansion's
Ramsey properties.

## Certified results and remaining obligations

1. **Verified:** fair non-starving component enumeration, exhaustion,
   minimal strong component increments and cofinal finite canonical
   presentations (#400, #412, #417, #433). The actual finite birth
   indices recover precisely the intrinsic component classes (#419).
2. **Verified:** the complete canonical unary operation is unchanged
   by the fair component chronology, including transfer from the
   literal closed finite stages (#418, #422, #427).
3. **Verified:** any componentwise injective local numbering makes
   the fair components consecutive in a strict vertex order of
   type ω, with the explicit predecessor-rank order equivalence
   (#439 and #457). This is not a proof of the **uniform chosen
   local ordered representative** convention in the manuscript.
4. **Verified:** arbitrary finite C-closed functional bases have
   the full extension property (#459); the actually constructed
   limit has the finite joint functional extension property and
   is homogeneous for finite closed functional partial isomorphisms
   (#512).
5. **Pending exact-head CI:** the clean direct finite-closed-base
   homogeneity corollary (#522) and the empty-base finite-age
   universality corollary (#511). Their statements do not add
   hypotheses to the already certified extension property.
6. **Still independent:** the uniform coherent local ordering
   required for the paper's ordered Ramsey expansion, and a
   fully general functional Fraïssé uniqueness theorem if that is
   included in the final statement.

The manuscript's full ordered proposition remains **PARTIAL**.
The unordered functional C₀ characterization should not be
confused with the additional Ramsey expansion assertions.
Neither the frozen manuscript text nor its validation markers
are changed by this status update.

## Adversarial mathematical checks

- **Referee on rank:** strict decrease is along genuinely lower
  components, never between two distinct vertices of the same
  component.
- **Referee on fairness:** every component has finitely many
  lower components, but infinitely many *other* components can
  have smaller closure rank. Hence global rank sorting fails;
  the minimum eligible priority is essential.
- **Referee on graph strength:** finite intrinsic components of
  an abstract closure algebra need not be minimal strong graph
  increments. Use finite canonical closed-heredity and
  frontloading, not a purely unary argument.
- **Referee on functional fidelity:** preservation is equality
  of all complete unary values, not an inclusion or a bound
  on old-neighbour sets.
- **Referee on countable scope:** a graph reduct isomorphism
  does not prove functional homogeneity or the prescribed
  ordered representative convention.

## 9 November internal adversarial status audit

- **Dependency/referee:** rank-minimal selection proves that an enabled
  component exists; least *numerical* eligible priority is needed for
  eventual fairness. The two minima must not be confused.
- **Predimension/referee:** #385 and #394 establish minimal strongness
  of an entire intrinsic-component interval. The separate closed-set
  theorem supplies global strongness; neither follows from arbitrary
  unary data.
- **Formal trust/referee (updated 13 November):** the full fair
  chronology and complete unary fidelity (#400, #402, #412,
  #417–#419, #422, #427, #433, #439 and #457), plus the
  all-closed-base functional extension and actual joint-step
  homogeneity (#451, #453, #454, #459, #512), are merged
  after their dedicated and repository-wide exact-head checks.
  The final direct corollary #522 and finite universality #511
  remain open pending fresh exact-head CI. Neither is treated as
  a manuscript certificate before verification.
- **Text/referee (updated 13 November):** a vertex order of type ω
  with convex intrinsic components is now certified for each
  componentwise injective local numbering. The prescribed
  **uniform local representative convention** remains open;
  arbitrary numerical labels are insufficient. Unlike the
  graph reduct identification of #375, the functional
  homogeneity result #512 explicitly preserves complete C-values.
