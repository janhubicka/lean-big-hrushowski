# A shorter C₀ intrinsic-component enumeration using finite layers

Date: 8 November 2026. Status: **English argument**; the finite-layer
closure lemmas are proposed in
`BigHrushovski/C0CountableIntrinsicLayers.lean`. The actual
ω-enumeration is **not yet Lean formalized**.

## Statement

Let `C : ℕ → Finset ℕ` satisfy

1. (x\in C(x)) for every x;
2. (y\in C(x)\Rightarrow C(y)\subseteq C(x)).

For each x put (P(x)=\{y:C(y)=C(x)\}). These are finite
nonempty intrinsic components. Their complete strict-lower set
is (L(x)=C(x)\setminus P(x)).

We want a listing of all components in order type ω such that every
component appears after all components from its strict lower set.
Each component must be an interval in the vertex enumeration.

## 1. Finite closed cuts without global priority searches

For n∈ℕ define

`S_n = ⋃_{i<n} C(i)`.

Every `S_n` is a finite set. By transitivity, it is
`C`-closed. Moreover `S_n⊆S_(n+1)`, and
`n∈S_(n+1)` by reflexivity. Consequently
`⋃_n S_n = ℕ`.

Put `D_n=S_(n+1)\S_n`. Every `D_n` is finite and
is a union of *whole* intrinsic components: if x∈D_n and
y∈P(x), then y∈S_(n+1) by closedness. If y∈S_n,
then x∈C(y)⊆S_n, a contradiction. Hence y∈D_n.

The nonempty layers partition ℕ into finite unions of components,
and every component appears in exactly one layer.

## 2. Sort within a finite layer only

The set of components contained in D_n is finite.
Order them by increasing `|C(x)|`, breaking ties
by `min P(x)`. This is a linear order on components,
not on vertices inside them. Every component is finite and
nonempty, so the minimum exists, and different components
have different minima.

If y∈L(x) and P(x) lies in D_n, then y∈S_(n+1).
If y∈S_n, its component was completed earlier.
Otherwise y lies in D_n, and the strict inclusion
`C(y)⊊C(x)` gives `|C(y)|<|C(x)|`.
Thus the component of y has been listed earlier
in that finite layer. No dependency is missed.

The rank-threshold version is already a concrete
finite mathematical statement:

`S_n ∪ {x∈D_n : |C(x)|≤r}`

is `C`-closed for every n and r. Ties within one
rank cannot carry strict dependencies between distinct
components, so appending components in arbitrary
tie-breaking order also keeps every intermediate prefix
closed.

## 2a. Finite peeling avoids building a sorter first

There is an even simpler existence proof within each finite layer.
Suppose Q is closed and `S_n⊆Q⊊S_(n+1)`.
Choose x∈S_(n+1)\Q minimizing `|C(x)|`.
Every strict predecessor of x belongs to S_(n+1)
by closedness of the target. If it were not in Q,
it would contradict the minimum. Consequently
`L(x)⊆Q`; moreover P(x) is wholly contained
in S_(n+1)\Q. The next set `Q∪P(x)` is closed
and strictly larger, and is still inside S_(n+1).

This is the new exact Lean endpoint
`exists_enabled_component_in_closed_pair`.
By finite induction on `|S_(n+1)\Q|`,
the entire layer admits a finite list of complete
component increments. The **induction and list**
are not yet formally constructed; the local step is.

An optional tie-breaking convention (smallest numerical
component representative among the minimum-rank
choices) would make the finite list canonical.
The existence proof itself does not require a
canonical tie breaker.

## 3. Concatenation has order type ω

Concatenate these finite ordered lists of components for
n=0,1,2,…, skipping empty lists. Every component occurs once,
and its full lower-component dependency set precedes it.

The resulting ordering has order type ω, rather than
ω² or a more complicated well-order: for each selected
component there are only finitely many earlier layers,
each with finitely many components. Infinitely many
components occur because their finite classes partition ℕ.

Finally, choose a finite linear order inside each component
and concatenate these finite blocks. The vertex order also
has order type ω. Every union of initial whole blocks is
finite and C-closed.

## 4. Strongness and the remaining ordered convention

If the countable graph has cofinal finite canonical C₀
presentations with exact complete unary values, its
finite C-closed subsets are globally strong.
The finite/two-frontloading and countable-transport
theorems in separate Track A PRs show that appending
one whole intrinsic component to a closed prefix
is a minimal strong step.

Consequently the component listing has the correct
minimal strong increments for the *graph*.
Its canonical complete unary values agree with the
given C because every dependency lies in a previous
component, and all finite canonical presentations
have exact original C-values.

The manuscript's **ordered expansion** also demands a
fixed representative of each ordered one-generated
closure type over earlier ordered components. Merely
using the numerical order inside a component is not
enough. This convention remains a distinct Lean proof
obligation, as does full functional Fraïssé uniqueness.

## Why this is shorter than the enabled-minimum algorithm

The earlier English plan chose at every step the
smallest-priority *enabled* unlisted component and
needed a fairness proof by induction on closure size,
then a finite-lower-component stabilization argument.

The layer construction needs neither a global minimization
over infinitely many enabled components nor a separate
fairness induction. Cofinality is automatic from
`n∈S_(n+1)`; rank sorting is performed only within
a **finite** layer. It avoids precisely the bad shortcut
of sorting all infinitely many components globally by
`|C(x)|`, which might starve every higher-rank
component behind infinitely many minimal ones.

## Formalization plan

- **Already proposed:** finite closed cuts, monotonicity,
  cofinality, component-saturated finite layers,
  strict dependency descent within each layer,
  and closed rank-threshold intermediate cuts.
- **Next:** implement a finite component-list sorter by
  the lexicographic key `(|C(x)|, min P(x))` and prove
  that every component is listed once with a closed
  prefix before it.
- **Then:** flatten the finite lists into a single
  enumeration, eliminate empty layers, prove order type
  ω and exact component intervals, and apply the separate
  countable minimal-step theorem.
- **Finally:** certify within-component canonical ordered
  representatives, complete unary agreement, and the
  functional Fraïssé characterization.

Until then the full enumeration proposition is PARTIAL.
