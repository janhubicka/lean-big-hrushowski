# Adversarial audit — extract complete split local graphs

16 October 2026

## Statement and reusable interface

For a finite graph G and disjoint actual vertex sets P,B,
the split carrier is P_subtype ⊕ B_subtype. The map sending an
old or fresh subtype vertex to its original graph vertex is
injective because P and B are disjoint, with full image P∪B.
The pullback graph is therefore isomorphic to the complete
induced subgraph G[P∪B] and records its old/fresh boundary.

The module proves:

* splitValue_injective and exact old/fresh/whole images;
* splitGraph_growthSparse_iff for the exact real-valued class C_F;
* splitGraph_minimal for minimal strict d-closed P<_d P∪B;
* splitGraph_exactSupport for the least strict d-closed hull
  of the complete old-neighbour set.

A prescribed minimal extension A<_d C has a canonical support
P=cl_A^d(N_C(B)), where B=C\A. The existing
canonical_dClosed_local_support lemma supplies the required
minimal P<_d P∪B and exact old-support hypotheses inside C.
This split interface then prepares the input to old-support
renaming (PR #165) and bounded normalization (PRs #164/#166).

## Five distinct adversarial mathematical checks

**1. No old/new identification.** The split map must be
injective on the entire Sum carrier. Injectivity within P
and within B separately is not sufficient; a cross-case
equality would identify an old and a fresh vertex and
destroy the extension. The disjointness hypothesis is used
explicitly in both cross cases.

**2. Full image.** The image of the split carrier must equal
P∪B, not merely lie within it. Otherwise a growth inequality
or minimal-step property on the whole local graph could be
transferred to the wrong finite endpoint. Both sides of the
old/fresh partition are checked individually.

**3. Nonedges.** The pullback graph includes the complete
induced graph G[P∪B], including all nonedges across the old
boundary and within the fresh block. This is essential
because graph predimension depends on the entire edge set,
not on a graph homomorphism image.

**4. Strict minimality and exact support.** Minimal strict
d-closedness and old-neighbour hull equality are distinct
requirements. The former does not imply that a chosen P
is the canonical support. The extracted graph transports
both properties with exact image/equality theorems.

**5. Scope of genericity.** The split graph extraction
does not construct the prescribed source embedding into
the countable birth graph or show any numerical cardinality
bound. It is a finite representation theorem, not a
finite-extension property. The remaining transport from
source support P to the literal embedded stage support Q
and the published closure bound must be combined with the
already certified countable local response.

For this module GREEN is permitted only after its exact
Lean declarations compile at a pinned final commit, with
standard-axiom and placeholder audits. The five roles above
are separated internal mathematical review passes, not
external independent referee certifications.
