# Track A: adversarial audit of intrinsic closure-components

Date: 8 November 2026. Source:
`BigHrushovski/C0CountableIntrinsicComponents.lean`.

The referee roles below are distinct internal mathematical checks; no
independent human or external-agent reviewers are claimed.

## Exact scope

Let `C:V→Finset V` have complete one-generated values:
`x∈C(x)` and `y∈C(x) ⇒ C(y)⊆C(x)`.
No finiteness of V is required.

Define the *intrinsic closure-component* of x as
`{y∈C(x): C(y)=C(x)}`. It is finite because C(x) is a finite set.

The proposed Lean results prove:

* `y∈component(x) ⇔ C(y)=C(x)`;
* every vertex lies in its intrinsic component;
* components with different full values are disjoint;
* in any finite canonical C₀ presentation, these intrinsic components
  are exactly the original minimal-strong component fibres, even if
  the witness chronological order differs;
* for `y∈C(x)` outside the component of x, the strict inclusion
  `C(y)⊊C(x)` holds, so `|C(y)|<|C(x)|`;
* the entire component of y lies inside the finite strict lower
  value of x.

This supplies a finite-predecessor relation on components of an
infinite functional C₀ presentation without choosing any order.

## Referee A — equality classes are finite without a finite carrier

A potentially dangerous definition is the infinite equality class
`{y: C(y)=C(x)}`. Reflexivity and equality imply `y∈C(x)`,
so the class is literally the finite filtered set `C(x).filter`.
No `Fintype V` premise is hidden in the result.

## Referee B — component membership versus full closure membership

An earlier component y may lie in C(x) without belonging to the
component of x. Therefore the membership criterion uses **equality
of the entire complete values**, not mere membership. A two-vertex
edge oriented backward in a canonical C₀ presentation is a direct
counterexample to equating the two notions.

## Referee C — no accidental assumption that a component is closed

In general, the intrinsic component of x is NOT closed under C:
it may depend on earlier components. The closure `C(x)` contains the
component together with all lower components. The new results only
assert `component(x)⊆C(x)`, not closure of the component itself.

## Referee D — source component identification is intrinsic

`unaryComponent_eq_canonical_component` uses
`FiniteC0.canonicalValue_eq_iff_index_eq` to compare equality
of complete value sets with equality of component indices. This
theorem holds on *any* finite canonical graph presentation, with no
requirement that two different witnesses order incomparable blocks
the same way, and no distinguished generator inside a block.

## Referee E — strict lower dependency really decreases

Transitivity gives `C(y)⊆C(x)` for every `y∈C(x)`.
The strict inequality does NOT follow from `y≠x`; distinct vertices
in one component have the same complete value.
It follows only when `C(y)≠C(x)`.
This distinction is essential for a well-founded dependency order.

## Referee F — full components, not representative points

If C(y) is a strict lower closure, **every vertex** z with
`C(z)=C(y)` lies in the finite strict lower set of x.
The proof checks the whole filtered component fibre,
rather than choosing one generator to represent it.
This is needed if components later become intervals in an
enumeration of the actual vertex set.

## Referee G — the remaining ordered enumeration

The preceding finite-predecessor facts do not yet provide a global
enumeration of type ω. A correct construction should repeatedly
choose the first not-yet-used component whose finite lower components
have all appeared; a fairness argument must show that no component is
postponed forever. It must also show the successor adds one **minimal
strong** graph component, using the existing finite closed hereditary
presentation theorem and the global finite canonical exhaustion.

The mere existence of finite equality classes in an abstract complete
unary closure algebra does NOT imply that those classes are minimal
strong graph increments; the concrete C₀ presentations are essential.

## Regression and Lean certification

The independent Python regression examines all **66,067**
finite unary operations on carriers of size at most four.
Among the **390** complete operations, it checks **1,516**
component instances and **1,250** strict lower dependencies, with
no mismatch in the finite mathematical calculations.

The exact Lean endpoints in `CheckC0IntrinsicCountable.lean`
are to be audited for only the standard logical assumptions;
the dedicated `track-a-intrinsic-countable.yml` workflow also
runs the no-placeholder scanner and the finite regression.

Until this exact revision passes kernel/axiom CI, these theorems
are proposed, not certified. Even after they pass, the paper's
closure-component enumeration and the countable `C₀`
Fraïssé/reduct proposition remain separate validation targets.
