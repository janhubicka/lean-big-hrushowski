# Independent mathematical proof-obligation audit: named C_F one-step response

16 October 2026

## Statement

Let S be a finite old source, H the complete desired graph on
S ⊕ B with B a finite linearly ordered new block, and
f:S→U_n a *prescribed* injective induced embedding with
d-closed image in the actual stage U_n. Let P⊆S be the
canonical old support, with P≤d S.

Assume the complete local graph H[P⊕B] satisfies
C_F membership, minimal strict d-closedness over P,
and exact old-neighbour d-closed support. Also assume every
old neighbour of B in H belongs to P and the numeric fresh
size |B|≤K(|f[P]|).

The lemma constructs the named stage support Q=f[P], the
canonical equivalence P≃Q fixing the prescribed vertex
values, the complete induced local graph transported over Q,
and its unique increasing ordered normalization.
The normalized graph determines an *actual* request r
from the bounded catalogue over Q in U_n.

It then constructs an induced embedding

    S ⊕ Fin(|B|) → M_F^dagger,

which fixes f[S] pointwise under the canonical birth map,
preserves/refects all old-old, fresh-fresh, and old-fresh
adjacencies, and has globally strictly d-closed image.
The returned map is genuinely constructed from the actual
tagged fresh block, not postulated by the extension property.

## Six separate hostile checks

1. **Literal old source.** The restriction P≃f[P] must use
   the given f, not an abstract isomorphic support. The
   source-old image of the complete map is fixed exactly by
   the birth embedding. Different actual supports yield
   different named request tags.

2. **Support d-closed in the whole old stage.** The local
   support P≤d S is not automatically closed in the stage.
   We use exact induced transport P≤d S to f[P]≤d f[S]
   and strict transitivity with f[S]≤d U_n to obtain
   Q≤d U_n. This gives a well-typed actual stage request.

3. **Full class admissibility.** The original local graph
   is in C_F, and transporting the old support plus
   increasing normalization must preserve *all induced
   edges and nonedges*. The exact growth predicate of
   the final normalized local graph is checked, not inferred
   from mere 2-sparsity or from the full old stage alone.

4. **Canonical support and size.** Minimal strict
   d-closedness and the exact old-neighbour hull are
   separate hypotheses. Both must pass through named
   old-base transport and increasing normalization.
   The numeric bound |B|≤K(|Q|) remains an explicit
   assumption in this lemma. The published growth bound
   is to be applied to derive it for arbitrary minimal
   C_F extensions, but is not smuggled in here.

5. **Boundary nonedges.** The target tagged graph could
   have an unwanted edge to an old source vertex outside Q
   unless its entire old/fresh boundary is characterized.
   The previously certified transportedLocal_full_boundary_iff
   and completeOneBlock_global statements supply *both*
   directions, including all missing crossing edges.
   The original hBack condition is indispensable.

6. **No circular genericity.** The construction only invokes
   the literal finite request catalogue and its globally
   d-closed one-block response; it never assumes the
   Fraïssé extension property it is meant to establish.
   What remains is the canonical support extraction of
   an *arbitrary* minimal A≤d C and transport of its
   local growth/minimality/support and numeric bounds
   into these exact hypotheses, followed by the already
   certified finite minimal-step induction.

## Validation conditions

Before marking GREEN, require the final Lean theorem to
compile and pass the integrated 68-step CI, including
standard logical axiom and no-placeholder checks. The
six roles above are separated internal adversarial
mathematical analyses, not independently hired/referee
agents or external human certification.
