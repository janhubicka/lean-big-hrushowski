# Countable C₀ closure-component enumeration: English proof plan

Date: 8 November 2026; validation-status update 12 November 2026. This is a proof plan, **not** a separate Lean certificate. It
isolates the remaining enumeration argument in
`prop:C0-free-generic` after the actual countable functional
Fraïssé/reduct theorem has been certified.

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
The **fair recursive finite prefixes and their exhaustion** were kernel-certified and merged in PR #412. PR #417 subsequently certified each vertex's unique component birth, exact fresh component equality and inclusion of the entire complete unary value at birth. What remains is turning those component prefixes into the manuscript's prescribed ordered vertex enumeration, including the uniform choice of order *inside* each component.

The intrinsic finite-class lemma alone does not justify this
step. The hereditary and frontloading theorems are needed.

## 4. The unary operation is unchanged

For any vertex x, its full value C(x) is contained in
the finite prefix ending with the component P(x), and
the induced finite presentation on that prefix has
exactly the inherited complete canonical value C(x).
Thus the enumeration's complete backward-reachability
value for every x equals the given function C(x).

No generator is singled out within a component.
For the *additional closure-respecting ordered expansion*
in the manuscript, the finite order **inside** each
component must be selected by a fixed representative of
its ordered one-generated closure type over the already
ordered lower components. Ordering every block by
numerical vertex labels alone need not satisfy the
uniform representative convention.

## 5. Countable functional Fraïssé identification

The unconditional functional-stage extension property and the
identification of the actual graph reduct with M₀ were kernel-certified
and merged in PR #375. The countable structure has finite closed covers,
a correct finite canonical age, and answers every finite functional
extension over each canonical stage.

To obtain the conventional Fraïssé extension property
over an **arbitrary** finite closed substructure A,
choose a finite canonical stage S containing A.
Free-amalgamate the requested finite functional extension
B of A with S over A using the already verified finite
two-sided functional amalgamation. The resulting finite
functional extension of S is realized over S by the
stage extension property, hence B is realized over A.

This gives universality and homogeneity by the usual finite
back-and-forth argument, using local finiteness of the
finite-valued unary closure. The details have not yet been
encoded as a global Lean theorem and must not be inferred
merely from the reduct isomorphism with M₀.

## Remaining independent Lean tasks

1. **Completed and merged:** the fair finite-prefix recursion and
   exhaustion (#412), enabled minimal strong steps (#400), and unique
   whole-component births and full values at birth (#417). The
   chronological order of components has type ω, but the manuscript's
   **ordered vertex expansion** is a separate assertion.
2. **Draft, not certified:** PR #419 constructs the literal finite
   birth index and shows its classes agree exactly with equality of
   complete unary values. PR #422 applies the certified component-order
   invariance (#418) to prove exact complete values given a canonical
   finite presentation of the literal fair prefix.
3. **Draft, not certified:** PR #427 constructs that canonical comparison
   presentation by restricting a cofinal finite stage and transporting
   it to the literal closed fair prefix. Its proposed conclusion is
   exact equality of complete unary values for the actual fair
   chronology, with no extra comparison assumption.
4. Construct and certify a **vertex enumeration of order type ω** that
   keeps each intrinsic component consecutive and obeys the uniform
   choice of ordered local representatives over the already ordered
   lower part. Arbitrary numerical orders within components do not
   establish that convention.
5. Extend the actual functional Fraïssé property from cofinal
   canonical stages to arbitrary finite closed substructures using
   the finite two-sided functional amalgamation theorem; formalize
   universality, homogeneity and uniqueness as applicable.

The manuscript's full proposition remains PARTIAL: the three draft
birth-index/complete-value bridge PRs await exact-head Lean checks,
and the selected ordered vertex representatives and functional
homogeneity remain separate obligations.

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
- **Formal trust/referee:** #400 is merged; #402 remains a draft Lean module with
  their own exact axiom/placeholder workflows. A passing isolated build
  is distinguished from the whole repository workflow. The draft #402
  do not upgrade a full manuscript validation marker.
- **Text/referee (corrected 12 November):** the order-ω component
  *exhaustion* is now proved; what remains is a suitable ordered
  **vertex** enumeration, proof of unary fidelity in its chosen
  chronology (draft #427), and the prescribed within-component
  representative convention. The reduct identification merged in #375
  does not establish those claims.
