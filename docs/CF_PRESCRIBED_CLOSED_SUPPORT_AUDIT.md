# Adversarial review: strict closure of the literal named support

16 October 2026

## Statement

Let f:S→U_n be the actual induced embedding of a finite old
source S into a tagged finite stage U_n, with f[S]≤d U_n.
Let P≤d S be the canonical old support of a minimal
strict d-closed extension. Then

  f[P]≤d f[S]≤d U_n.

The first inclusion is the exact strict d-closed transport
through an induced injection; the second is the given
closed source image. Transitivity yields f[P]≤d U_n.
The actual image Q=f[P] is the literal support indexed by
the finite request catalogue, not an abstract copy of P.
Since U_n is globally d-closed in the countable birth graph,
Q is globally d-closed there too.

## Five hostile proof checks

1. **Exact names.** The result uses the image of the actual
given embedding f. Replacing it by an arbitrary isomorphic
support Q' would not necessarily extend the prescribed e
or retain the correct old-neighbour boundary.

2. **Intermediate predimension.** Strict d-closedness of P
in S is transported only because f preserves and reflects
all edges and nonedges within the whole old source. Mere
graph homomorphism does not suffice.

3. **Strict rather than weak.** The proof composes two
IsDClosed inclusions, not IsStrong. Minimal C_F extensions
and their Fraïssé embeddings use strict inequalities.

4. **Global closure is not automatic.** The finite support
is first proved d-closed in its finite stage. The separate
already certified global finite stage closure is then used
to obtain global d-closedness in the countable birth graph.

5. **Not the response yet.** The lemma fixes the actual
support, but it does not construct the prescribed local
graph, verify the canonical support hull, choose the
ordered fresh block, or realize the requested extension.
Those use split graph extraction (#167), named support
equivalence (#171), growth normalization (#166), numerical
inverse (#172/#174), and exact global response (#162).

This review consists of separate internal hostile mathematical
checks, not independent human or external referee reports.
Do not mark it green until the final Lean build passes
standard-axiom, placeholder and declaration checks.
