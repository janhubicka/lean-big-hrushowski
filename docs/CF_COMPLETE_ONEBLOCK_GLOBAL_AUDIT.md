# Adversarial audit: complete globally closed one-block response over a fixed source

16 October 2026

## Main assertion

A real finite tagged request r has a literal support P in an old
stage U and a complete ordered fresh block Fin(m). Let f:S→U be an
injective old-source embedding with strictly d-closed image.
Suppose H is the desired graph on S⊕Fin(m), and its complete
adjacency relation is the free extension over P:

* old--old edges agree with the old stage along f;
* fresh--fresh edges agree with the complete code of r;
* an old--fresh edge occurs exactly when the old image f(s)
  is one of the named P vertices and the corresponding edge
  occurs in the local code.

The map sending old s to Sum.inl(f(s)) and fresh i to the actual
tagged vertex Sum.inr(r,i) is injective and induced in the
*whole* next finite level. Its vertex image equals precisely
the old-source image plus the chosen tagged block. The
already certified selected-sub-batch factor theorem makes
this finite image d-closed in the full simultaneous batch,
and the certified global stage theorem upgrades it to global
strict d-closedness in the countable birth graph.

The old source is fixed pointwise by the birth map. This is
a full one-block extension theorem, not just a theorem about
the much smaller support+block induced graph.

## Five hostile mathematical referee checks

1. **Boundary nonedges.** The inducedness of the local support+
block graph does NOT by itself prohibit an extra edge from the
fresh block to an old vertex outside the support. The separate
exact old--fresh boundary lemma (PR #176) proves that the tagged
batch introduces no such edges. The full-source theorem uses it
in both directions of the adjacency equivalence.

2. **Literal source and fresh tags.** An old source vertex f(s)
has a Sum.inl tag; each new vertex has the pair (r,i) under
Sum.inr. The complete map is injective because f is injective
and the tags cannot collide. A different request with the same
abstract code does not supply additional edges.

3. **Exact finite image.** The image is the full old source
plus exactly one selected fresh block, rather than a subset
of the whole batch or a copy of the small support. This
identity is necessary before applying strict relative
closure and is checked by decomposing the disjoint Sum
carrier into old and fresh parts.

4. **Strict closure through unrelated requests.** Knowing the
source+block is d-closed in the induced old-plus-block prefix
does not imply closure in the whole simultaneous level.
The previously certified arbitrary-selected-block theorem
handles interference from every other fresh request, and
global stage closure then handles every later level.

5. **Remaining normalization scope.** The theorem starts with
a concrete tagged request r and an H whose three categories
of adjacency have been explicitly matched to that request.
It does not manufacture r from an arbitrary minimal A<_d C
over a prescribed embedding. The final genericity bridge
must combine split graph extraction (#167), the canonical
old support and named equivalence (#171), admissible bounded
normalization (#166), exact growth size (#172/#174), and the
prescribed source lift (#173). No automatic order-preserving
global self-embedding or functional R/H recovery follows.

The five roles are separate internal adversarial mathematical
reviews and are not reports from independently instantiated
external human referees. The exact Lean theorem endpoints
remain provisional until they pass the integrated build,
standard-axiom and no-placeholder checks.
