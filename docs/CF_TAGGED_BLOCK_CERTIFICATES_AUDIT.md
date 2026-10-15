# Adversarial audit: named tagged block domains and exact supports

15 October 2026 — finite graph-predimension library.

We identify the old-stage vertices in a tagged simultaneous graph,
the actual image of the closed support of each request, and its
own disjoint fresh block. The exact code-to-image identities are
needed to apply the already verified local minimality and d-closed
support-transport theorems without changing vertex names.

## Four independent adversarial mathematical checks

**1. Tagged carrier and disjointness.** The fresh vertex (r,i)
carries the *entire* local request r, including its literal support.
Two different requests can have isomorphic ordered codes or the
same support; their fresh vertices are still distinct. No fresh
vertex equals an old vertex. The proofs of disjointness use exact
sum/sigma constructor equalities, not generic cardinality.

**2. Actual old support.** The old image of the normalized local
code is the image of the literal subset r.support in the finite
old stage. It is not merely an isomorphic copy. The support is
strictly d-closed in the induced old stage, transported from
the source graph through the certified induced old embedding.
This claim does not assert closure in the *entire new batch*.

**3. Complete local copy and closure.** The image of the whole
local type equals precisely support(r) ∪ freshBlock(r).
By exact induced adjacency and the strict d-closure image
theorem, the local minimal step survives in this **finite
induced image interval**. The complete old-neighbour set,
not only the neighbours of the first new vertex, transports
to the tagged image. Its least strict d-closed hull over the
actual support is exactly that actual support.

**4. Global-versus-relative referee.** Minimality and exact
support in the finite local copy do not by themselves imply
that the request's support is d-closed in an arbitrary
intermediate union of many blocks. The next step must derive
this from the original support's d-closedness and the
transitivity of the old-stage inclusions. In particular, the
proof may not infer membership in the restricted growth
class C_F merely from these graph-theoretic properties.

## Independent bounded regression

The existing complete tagged-batch checker is strengthened:
for every small actual request, it compares the induced
predimension of every local subset, the complete old-neighbour
set and its d-closed hull, and verifies that the actual old
support is d-closed in the old induced graph. This supplements
the general Lean theorems rather than replacing them.

The exact lemma endpoints are
CFStageCatalogue.localOld_image_eq_taggedSupport,
localFresh_image_eq_taggedBlock,
localUniv_image_eq_support_union_block,
taggedBlock_disjoint_old, taggedBlocks_disjoint,
taggedSupport_dClosed_old, taggedLocal_minimal and
taggedLocal_exactSupport.

Do not promote this group to certified status until the
integrated Lean build, standard-axiom audit and placeholder
scan pass. The full finite multi-block closure theorem for the
specific batch, class C_F membership and countable genericity
remain separate obligations.
