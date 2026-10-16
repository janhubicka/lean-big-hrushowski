# Adversarial audit: complete boundary after old-support transport

16 October 2026

## Mathematical content

A finite desired graph H is presented on an old carrier V
together with a finite linearly ordered fresh block B.
Its canonical old-neighbour support P is a subset of V.

Restrict H to P⊕B, identify P by an induced equivalence
e:P≃Q with the *actual* named target support Q, and
enumerate B increasingly by Fin(card B). The resulting
transportedLocalGraph carries the complete local graph
over Q, including all its nonedges.

Suppose f:V→U is the given injective old embedding and
(e p).val=f(p.val) for every p∈P. Suppose also that
every old neighbour of a new vertex lies in P, as
supplied by the canonical old-support theorem.
Then for every old x and fresh ordinal i:

  H(x,new_i)
    iff exists q∈Q, q.val=f(x) and t(q,new_i).

This is precisely the boundary hypothesis expected by the
complete tagged one-block response. In particular, old
vertices outside Q have no new neighbours, and the proof
does not merely preserve positive edges: it reflects all
missing boundary edges.

## Five hostile mathematical referee checks

1. **Exact vertex names.** The old Q is the literal target
image of P under the prescribed f. Replacing it by an
isomorphic but distinct old support would not extend f
pointwise, and the boundary matching may fail.

2. **Fresh order.** The bijection from Fin(card B) to B is
the increasing equivalence. It must not permute the old
support or produce a different fresh vertex than the
one used by the prescribed extension.

3. **Old-neighbour support.** The forward direction uses
the explicit hypothesis that an edge to a fresh vertex
forces membership in P. This is stronger than saying
P≤d V: d-closure alone does not forbid edges crossing
from new vertices to old vertices outside P.

4. **Reverse direction and injectivity.** If a named
support q has the same image f(x), then q=e(p) for
p=e^{-1}(q), and injectivity of f forces p.val=x.
Without injectivity, an edge at a different support
vertex might be mistaken for an edge at x.

5. **No premature genericity.** This theorem compares
a split local graph and the transported complete
normalized code. It does not itself construct the
finite tagged request, prove its size is bounded,
or establish strict d-closedness of its image.
Those are separate certified or pending theorems.
Its role is to discharge the boundary hypothesis of
the complete one-block global response PR #177.

All five checks are internal adversarial mathematical
passes, not external independent referee reports.
GREEN validation requires the exact Lean declarations
to pass integrated build, standard axioms and the
placeholder scan at their final commit.
