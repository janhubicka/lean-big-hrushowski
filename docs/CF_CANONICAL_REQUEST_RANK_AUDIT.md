# Adversarial audit: canonical ranks of literal C_F requests

28 October 2026

## Scope

For a **fixed finite old graph equipped with a linear order**, the request
catalogue is finite. The strict request order was proved in #232. We define

    rank(r) = |{s : StageRequest // s <_lex r}|.

The new theorem `requestLexLt_iff_rank_lt` states that this explicit
integer rank both preserves and reflects the manuscript's support-tuple,
fresh-size, full-adjacency-matrix comparison. It does **not** replace the
manuscript order by an arbitrary `Fintype.equivFin`.

## Role-separated hostile checks

1. **Strictness:** If r < s, every predecessor of r precedes s by the
   already-checked transitivity theorem. The element r itself precedes s
   but not r. This proves a *proper* subset, hence strict cardinal growth.
   A non-strict inclusion would not be enough.
2. **Duplicate codes:** Trichotomy of literal request records comes from
   the complete dependent-key injectivity in #232. Equal supports and
   same fresh size alone are insufficient: every local adjacency bit,
   including internal fresh edges and nonedges, is needed.
3. **Empty catalogue:** No requests implies the rank theorem is vacuous;
   the construction introduces no phantom vertex and presupposes no
   nonempty minimal extension. Existence of a singleton empty-support
   request remains its own condition.
4. **Empty predecessor set:** The minimal request has rank zero, as
   expected; the proof makes no assumption of an earlier request.
5. **Order reflection:** If rank(r) < rank(s), trichotomy rules out r=s
   and s<r, the latter by strict rank monotonicity. The equivalence
   establishes exact finite-order correspondence, not only injectivity.
6. **Stage-order gap:** `[LinearOrder U]` is an explicit hypothesis.
   The canonical linear order on each recursively constructed
   `(stage F K n).carrier` and its consistency under `Sum.inl`
   are not yet supplied. Thus this is a finite-order interface, not
   a proof of the full C_F enumeration order or embedding monoid.

## Verification contract

Only after a successful full Lean build plus the standard-axiom and
placeholder audits may the four named theorems be marked certified.
For now, this note is a mathematical and source audit; the manuscript's
countable-order and finite-lifting claims retain PARTIAL/TODO status.

No separate human referees have been consulted; the adversarial
perspectives above are independent *checks* of the proof obligations.
