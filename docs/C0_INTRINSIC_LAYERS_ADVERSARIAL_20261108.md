# Adversarial audit: finite unary layers for C₀ enumeration

Date: 8 November 2026. Internal role-separated mathematical audit:
the roles are **not** additional human referees. The exact new Lean
proofs are still pending kernel and axiom CI.

## Referee A: closedness, not merely increasing supports

`S_n=(range n).biUnion C` is finite by construction.
For any x∈S_n, some i<n has x∈C(i). The complete-unary
transitivity axiom gives the **entire** C(x)⊆C(i)⊆S_n.
No arbitrary iteration or countable union is used to
prove the finite cut closed.

## Referee B: the next layer comes from one generator

The exact successor identity is
`S_(n+1) = S_n ∪ C(n)`, and hence
`D_n = C(n) \ S_n`. These are literal finite
set equalities, requiring no closure axioms.
In particular the finite sorting problem at layer n
uses only vertices of **one** finite complete closure.
This observation also rules out an accidental
ω²-style construction by processing all possible
component ranks globally.

## Referee C: fixed labels force exhaustion

The generator n belongs to S_(n+1) by reflexivity.
Consequently the sequence of finite cuts covers the
literal Nat carrier and cannot stall forever. This
avoids an unproved fairness postulate for the eventual
enumeration; it does not itself construct the list of
components.

## Referee D: layers do not split intrinsic components

If x∈S_(n+1)\S_n and y has exactly the **same entire**
C-value, then y∈C(x)⊆S_(n+1).
If y∈S_n, closedness of S_n gives
x∈C(y)⊆S_n, a contradiction.
Therefore y lies in the same fresh layer.
The argument does not confuse equality of C-values
with mere membership in C(x).

## Referee E: dependency rank decreases strictly

For y∈C(x)\P(x), transitivity says C(y)⊆C(x),
and non-membership in P(x) rules out equality.
Hence `|C(y)|<|C(x)|`. A predecessor of
a component in D_n is either in an earlier S_n,
or in D_n with lower rank. An infinite globally
rank-sorted sequence is **not** inferred.

## Referee F: no partial rank closure

The rank-threshold cut
`S_n ∪ {x∈D_n: |C(x)|≤r}`
is genuinely closed under every C-value:
for a new x and y∈C(x), either y was old,
or y belongs to D_n and `|C(y)|≤|C(x)|≤r`.
These cuts take every member of an intrinsic component
together because equal C-values have equal cardinality.

## Referee G: whole-component segments at a tied rank

The new `unaryFiniteLayer_segment_closed` theorem handles
an arbitrary finite set t of **whole** components in the
current layer. It requires all lower-rank components in the
layer whenever t contains a higher-rank component, but it
does not demand that *every* component of the current tied
rank be chosen. For x∈t and y∈C(x), either y is old,
or y is in the current layer. Equality of full values
keeps y with x inside the same whole component. Distinct
values force a strictly lower rank, whose component is
present by the lower-rank condition. This is the exact
intermediate-cut property needed by a finite sorter.

## Referee H: a minimal-rank component always exists

For a proper finite closed inclusion S⊊Z, use the same
minimal-cardinality selection pattern as the repository's
existing `MinimalExtensions.exists_minimal_choice`:
take the minimum element of the finite image
`{ |C(x)| : x∈Z\S }` and an x realizing it.
If y∈L(x), closedness of Z forces y∈Z. If y∉S,
then y is another candidate with strictly smaller
rank, contradicting minimality. Hence L(x)⊆S.

Moreover P(x) lies in Z\S because both S and Z
are closed and all vertices in P(x) have the same
complete unary value. Thus S∪P(x) is again closed,
properly extends S, and stays within Z. This is
formally stated as
`exists_enabled_component_in_closed_pair`.
The method requires no infinite priority search.

## Referee I: adversarial exhaustive regression

The independent Python regression enumerates **all 66,067**
set-valued unary maps on carriers of size at most four.
It checks the claims on all **390** reflexive-transitive
complete maps: 1,906 finite cut/layer checks,
1,516 component-in-layer checks, 1,250 strict
predecessors, 9,380 rank-cut closedness checks, and
3,289 lower-rank-closed whole-component segments among
4,562 candidate finite layer segments, and **7,588**
minimal-rank component choices across 6,071
proper closed pairs.
No counterexample was found in a separate local run.
The script is included in dedicated CI but is not
a substitute for Lean kernel proof checking.

## Referee J: the missing ω-ordering and graph theorem

This PR proves the finite combinatorial ingredients
only. A finite sorter and concatenation into a literal
order-type-ω enumeration are **not yet Lean formalized**.
Neither graph minimal strongness nor the correct
within-component representative convention follows
purely from an arbitrary unary closure algebra.
Those are separately recorded Track A proof obligations.

## Verification gate

`CheckC0IntrinsicLayers.lean` prints the exact axioms
of thirteen new theorems. The dedicated workflow builds the
new module, runs the axiom checker, placeholder scanner,
and exhaustive regression. Exact CI on this head and
its parent intrinsic-component branch must pass before
merging or promoting a manuscript validation marker.
