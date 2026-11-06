# Track F — finite enumerations versus labelled linear orders (6 November 2026)

**Mathematical point.** A finite enumeration (e: \operatorname{Fin}(n)\cong V)
determines a strict linear order on the actual labelled vertex set by
(x <_e y\iff e^{-1}(x)<e^{-1}(y)). Two bijective enumerations of the same
labelled domain produce the same order relation **only when they are
equal**. The proof transports their equality of order relations
to a finite ordinal order automorphism, which Mathlib proves is
the identity.

Consequently the finite code fibre counted by
`N0LocalCodeFibre.localCodeFibre_card` represents exactly that many
*distinct labelled linear order relations*, not merely that many
enumeration objects. This addresses a genuine part of the finite
degree formula's counting correspondence.

**Adversarial referee panel (internal checks):**
1. The order is on the **fixed labelled set**, not on an
   isomorphism-class quotient of unordered copies.
2. Injectivity relies on bijectivity of the enumeration;
   a noninjective listing could repeat labels and invalidate it.
3. Two sinks swapped by an automorphism can have the same directed
   adjacency code but yield distinct labelled orders.
4. The relation satisfies strict irrefl., transitivity and
   totality; empty and one-point domains are included.
5. The count is the **embedding**-oriented count; dividing by
   `|Aut(A)|` for image copies is a later separate convention.
6. This proof still does not assemble entire permitted global
   orders from component prefixes. Require Lean CI, axiom audit
   and the independent finite regression before marking validated.

No manuscript changes. No infinite big Ramsey assertion is proved.

## Reconstructing the component order from a vertex enumeration

The new `N0ComponentFirstPositions.lean` associates to an actual
component its **first occupied position** in a bijective vertex
enumeration. Every SCC is nonempty, and different SCCs have
different first positions. If the enumeration is successor-first,
then the first positions of components strictly respect the
intrinsic SCC dependency order. The proof chooses a vertex
occupying the first position of the higher component and uses
proper reachability to *every* vertex of the lower component;
the minimum lower-component position must therefore be earlier.

### Additional internal adversarial referees

- **Partition referee.** Components are subsets of the actual
  domain, rather than artificial block labels; membership recovers
  the unique SCC. Distinct SCCs cannot share the first vertex.
- **Order referee.** Successor-first means every proper successor
  vertex occurs before its source, not only that some witness
  pair happens to be correctly ordered.
- **Interval referee.** This lemma does not assume component
  intervals, so it does **not** yet give the full uniqueness of
  global block decompositions. That extra hypothesis must be
  checked when reconstructing a permitted order.
- **Finite regression referee.** Independently exhaust all 653
  orientations on at most four labelled vertices and all 15,074
  vertex enumerations. Check 3,810 successor-first enumerations
  and 5,168 component dependency comparisons, plus a reversed
  two-vertex arrow as a negative case.
- **Certification referee.** Require the exact new Lean endpoints
  to pass the kernel and axiom audit; a successful preexisting
  umbrella build does not suffice.

This remains finite and does not establish the manuscript's
recurrence or big Ramsey degree theorem.

## SCC interval recovery (additional adversarial round)

The same module now defines the literal interval condition on a
bijective vertex enumeration: no vertex outside an SCC may appear
strictly between two vertices of that SCC. Distinct SCCs have
disjoint carriers. Under this interval condition the order of
their first positions is equivalent to the condition that
**every** vertex of the earlier SCC precedes **every** vertex
of the later SCC. Thus the block order is determined by the
global order, not an extra choice.

Independent regression checks all 15,074 complete enumerations
of 653 oriented graphs on up to four labelled vertices. Of these,
13,730 have SCC intervals, and 131,184 ordered pairs of distinct
SCCs were tested for equivalence of first-position order and
complete component separation; all pass. The additional
successor-first checks remain 3,810 enumerations and 5,168
dependency comparisons. No theorem about canonical local code
orders follows solely from this interval recovery result.

Adversarial checks: the relation is **on labelled vertices**;
the intervals are disjoint and nonempty; an arbitrary
enumeration can interleave two components, so the interval
hypothesis is essential. The count `ell(A)` is recovered only
after also imposing the successor-first condition.

## The recovered legal finite ranking

`rankingFromEnumeration` equips the actual finite SCC type
with the strict order induced by first occurrence, then uses the
unique increasing bijection between any finite linear order
and a consecutive finite ordinal. This is an actual
`ComponentRanking`, not merely a numerical first-position
function. If the original vertex enumeration is successor-first,
the ranking is a legal linear extension of the SCC dependency
order by `rankingFromEnumeration_isLegal`.

Together with the interval-recovery lemma, this supplies the
component-order extraction direction of the desired finite
bijection. What is still missing is the reverse reconstruction
of a complete permitted vertex order from the ranking and its
compatible **local code orders**, with a uniqueness proof.

Adversarial reviewers checked that the rank is injective
because SCCs have disjoint nonempty vertex sets, that it is
consecutive by the finite-order isomorphism (not by
the potentially gapped numerical first positions), and that
the dependency order is inherited from actual successor-first
vertex order. These endpoints require renewed Lean CI.

## Reconstruction uniqueness (further finite audit)

The theorem `enumeration_eq_of_same_component_order_and_local_orders`
proves injectivity of the decomposition of a component-interval
vertex enumeration into (a) the SCC order and (b) the
induced local order on each SCC. Cross-component comparisons
are recovered from first positions, and internal comparisons
are precisely the local-order data.

The independent regression checks all 13,730 component-interval
enumerations of 653 small orientations, rejecting any duplicate
(component order, internal component orders) data.
Interleaving an isolated vertex with a directed 3-cycle
shows that the interval hypothesis cannot be omitted.

This is only the uniqueness half of global reconstruction.
Existence and compatibility with canonical local codes over
the already ordered lower part remain unproved.
No infinite big Ramsey assertion or manuscript marker changes.
