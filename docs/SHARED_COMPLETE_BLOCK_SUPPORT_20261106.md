# Adversarial review — complete block value forces old support image

6 November 2026. Internal role-separated mathematical checks, not
outside human referee reports.

## Statement

Let P,B and Q,C be two finite old-support/fresh-block pairs,
with P∩B=Q∩C=∅. For an injective f on the entire source,
if f[P∪B]=Q∪C AND f[B]=C, then necessarily f[P]=Q.
The proof derives equality, rather than only inclusion.

## Independent hostile roles

1. **Complete-value referee:** replace equality of f[P∪B]
   with inclusion and the conclusion is false; the theorem
   retains two-sided complete value equality.
2. **Block-surjectivity referee:** mapping B merely into C
   does not force the correct support, since C can contain
   unmapped vertices; the theorem requires f[B]=C.
3. **Injection referee:** without injectivity, an old support
   vertex could collide with a fresh block image, and
   the forward inclusion fails. The theorem keeps hf.
4. **Disjointness referee:** both source and target support
   and block must be disjoint; target Q∩C=∅ rules out
   a target support element coming solely from B.
5. **Literal values referee:** sets are actual Finset U/V;
   the conclusion is literal equality f[P]=Q,
   not equality of abstract graph isomorphism types.
6. **Empty cases referee:** empty support or empty block is
   allowed. No distinguished vertex is selected.
7. **Reuse referee:** the theorem is free of predimension,
   order, functions and birth levels, so it applies to
   both C_0 and C_F block/component presentations when
   their actual complete values are known.
8. **Uniqueness referee:** this resolves only target old
   support image recovery. Equality of ordered adjacency
   codes still requires complete inducedness and increasing
   order; ordinal position rigidity is a separate lemma.
9. **Kernel referee:** one exact axiom endpoint is registered
   in CheckAxiomsSharedBlockSupport.lean. Full build,
   standard-axiom audit, placeholder scan and finite
   regressions are required before claiming verification.
10. **Manuscript referee:** no mathematical prose or green
    marker changes here. The full finite unique lifting,
    restriction/composition and embedding monoid stay partial.

These are hostile mathematical reviewer roles implemented as an
explicit proof audit, not a report from external referees.
