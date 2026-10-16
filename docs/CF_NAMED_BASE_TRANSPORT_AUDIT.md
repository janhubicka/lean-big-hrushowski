# Adversarial audit — transport of a local extension to a named old support

16 October 2026

A minimal local graph originally has old support P and a
complete fresh block B. To realize it over a prescribed copy
of P in a finite stage, the actual named stage support is Q.
An equivalence e:P ≃ Q carries the old vertices to Q and
leaves B unchanged. Pull back the entire local graph along
e.symm on the old side and identity on the fresh side.

This is a graph isomorphism. The exported statements verify:
  * the complete growth-function inequality, not just 2-sparsity;
  * preservation and reflection of minimal strict d-closedness;
  * exact transport of the old-neighbour d-closed hull;
  * agreement with the named induced graph on Q provided e is
    induced on the old base.

The graph has the same cardinality and every original nonedge
continues to be a nonedge. The original order on B is unchanged.

## Five adversarial mathematical checks

**1. Literal old names.** The new old vertices are precisely
those of Q. The result must not add another abstract copy of
P or identify two actual supports. The transport uses an
equivalence between P and Q, and leaves the fresh block B
untouched; a separate theorem must construct this equivalence
from the embedding of an arbitrary finite source.

**2. Exact inducedness.** A map preserving only positive edges
would be insufficient: additional edges change δ and can
destroy strict closure and membership in C_F. The old/base
isomorphism transports all adjacency equivalences, including
nonedges crossing old/fresh and inside B.

**3. Strict versus weak.** The minimal-step statement uses
IsMinimalDClosedStep and the induced-image theorem, not
IsMinimalStrongStep. The latter is a different closure notion
and cannot substitute for the sparse-graph C_F argument.

**4. Hull equality.** Preservation of the vertex set P as a
set is insufficient: the proof must transport the old-neighbour
set and its least *strictly d-closed* hull. It invokes the
certified canonicalOldSupport_image and injectivity of the
whole local graph equivalence.

**5. Remaining source normalization.** This module starts
with an equivalence e:P≃Q and a complete graph on P⊕B.
It does not itself construct that graph from a given
minimal extension A<_d C and prescribed embedding of A
in the countable limit. The published uniform size bound,
ordered normalization by Fin(|B|), and the certified global
response must still be composed to obtain full genericity.

All statements need a final passing Lean build, standard
logical-axiom report, placeholder scan and mathematical audit
before being marked green in the manuscript.

These referee roles are deliberately separated internal
hostile proof checks, not external independent human reports.
