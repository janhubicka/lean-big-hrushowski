# Track B adversarial audit: unique literal target request

1 November 2026. Internal mathematical referee roles, not
independent external human reports.

## Exact endpoint

A finite StageRequest is fully identified by (i) its **literal**
old support, (ii) the number of fresh vertices and (iii) its
complete ordered adjacency matrix, including every nonedge.
The source and target may have different old carrier types.
For a genuinely partial old map `e : SupportCarrier U S → V`,
any target request with precisely the transported support image,
source fresh size and source full adjacency code is **equal**
as a dependent record to `transportGrowthStageRequest_partial`.

## Hostile checks

1. **Support labels:** equal abstract local isomorphism types
   do not suffice; support equality is literal equality of
   finite subsets of the actual target old carrier.
2. **Adjacency:** knowing only positive edges or only
   old-neighbour incidence would not determine the local type;
   the ordered matrix includes old-old, old-fresh, fresh-fresh
   bits and their complements.
3. **Size:** equality of supports and edge matrices alone does
   not identify fresh-size-dependent records; size is explicit.
4. **Dependent records:** the source and target request
   constructors carry proof-valued boundedness and strict
   closure certificates. Complete-key injectivity establishes
   equality of those proof-bearing records in Lean, rather
   than assuming definitional equality.
5. **Empty target:** `U≠∅, S=V=∅` is covered. The theorem
   never uses a total source-stage function.
6. **Uniqueness scope:** the theorem proves a single request
   tag is forced *when the complete code is known*. It does
   not yet derive code preservation from an arbitrary
   functional embedding or prove uniqueness of the full
   selected batch/finite lift.
7. **Kernel:** two `#print axioms` endpoints are listed.
   Full Lean CI, placeholder scan and finite regressions are
   required before a manuscript marker is made green.

Next: use complete b-value transport and inducedness to derive
the target support/code of an arbitrary embedding, and combine
tag rigidity with finite block-ordinal rigidity and induction.
