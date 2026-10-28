# Adversarial audit: ranked orders on the actual C_F birth carrier
28 October 2026

## Scope of this PR

A literal birth vertex has three pieces of data: (n, r, i), its
birth level, the exact finite request tag, and its chosen fresh
ordinal. For every family of numerical request ranks at each
level, compare (n, rank_n(r), i) lexicographically.

This module proves irreflexivity, transitivity, comparability
of distinct vertices for injective ranks, and agreement with
the natural chosen order of the fresh ordinals **inside each
complete birth block**. A noncomputable arbitrary injective
ranking exists because the request type at each stage is finite.

**This is NOT yet the specific order selected in the paper.**
The manuscript orders request tags by (1) the increasing
support tuple relative to the inherited old order, then
(2) the ordered local adjacency code. The arbitrary Fintype
rank used as a witness here need not coincide with that
lexicographic request order. A future specialization must
define a ranking by these exact keys and prove coherence of
the inherited old-stage order. The present module is
therefore an API and order-theoretic reduction, not a proof
of the complete concrete-order bridge.

## Twelve adversarial checks

1. **No equality across types.** A request tag r at level n has
   a dependent type depending on n. The code compares request
   ranks only after comparing birth levels and preserves the
   distinct literal request tags.
2. **Finite request injection.** If rank_n is injective, distinct
   requests at the same level cannot receive the same code.
   A non-injective arbitrary ranking would fail linearity.
3. **Fresh ordinals.** For vertices of one complete request tag,
   both level and request rank coincide; only their Fin-index
   comparison remains, so the chosen block order is exact.
4. **Earlier stages first.** n<m implies every vertex born at n
   precedes every vertex born at m, independently of request
   ordering.
5. **Strict linearity.** Trichotomy follows from the finite
   numeric triple code *only because the complete vertex code
   is injective*. Arithmetic trichotomy alone would not prove
   distinct vertices comparable otherwise.
6. **No accidental quotient.** All code and order functions
   are defined on the actual Sigma birth carrier; no
   isomorphic replacement or quotient is introduced.
7. **No assumed global order.** The proof establishes its
   relation from Nat inequalities, rather than presuming
   an unrelated LinearOrder instance on request records.
8. **Mathematical versus chosen order.** The arbitrary
   Fintype.equivFin rank may depend on classical choices.
   The manuscript's exact deterministic support-and-code
   order is an additional obligation; do not mark its
   current partial validation statement GREEN from this PR.
9. **Level-lifting dependence.** The later unique coordinate
   lifting lemma explicitly invokes lexicographic comparison
   of support tuples. Replacing that ordering with an arbitrary
   request order in the manuscript may invalidate the proof,
   even though root recovery itself would still work.
10. **Root identification.** BirthBlockOrderCompatible follows
    for *every* request ranking, without injectivity. The
    latter is necessary only for a strict **total** order on
    unrelated request tags.
11. **All finite cardinalities.** The request type may be
    empty. Fintype.equivFin and injection on the empty type
    remain meaningful; no inhabitance assumption is needed.
12. **Kernel validation.** Ten exact theorem endpoints must
    pass full integrated Lean compilation, standard axiom
    audit, placeholder scan, and regressions. These role-
    separated hostile mathematical checks do not claim
    independently spawned external referees.

## Next step

Construct the actual request rank using the increasing support
tuple (as ordered by the recursively inherited old stage) and
the complete ordered local graph adjacency bit code. Prove it
is injective and agrees with the order of the manuscript, then
instantiate the current lexicographic triple-order API. Only
then should the last PARTIAL manuscript marker be promoted.
