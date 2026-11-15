# Track E — countable partial R/H embedding equivalence

13 November 2026.

## Statement

Let \(M\) be the **actual countable C_F birth presentation**
and let \(b\) be its complete auxiliary unary function. The
published functional presentation instead records the
set-valued R-operation and the partial H-operation, whose
domain consists precisely of finite sets of genuine birth roots.

For a self-map \(f:M\to M\), suppose injectivity, induced graph
adjacency and nonadjacency, canonical birth-order preservation,
and preservation and reflection of the birth-level preorder.

The existing closed-source equivalence theorem, applied to the
literal source \(X=M\), gives:

\[
 \forall v\, f[b(v)]=b(f(v))
 \quad\Longleftrightarrow\quad
 \begin{cases}
   f[R(v)]=R(f(v)) & \text{for every }v,\\
   f[H(S)]=H(f[S])&\text{for every defined }H(S),\\
   H(S)\text{ defined}\iff H(f[S])\text{ defined}
      &\text{for every finite }S.
 \end{cases}
\]

The converse is not obtained by treating H as a total function.
It uses the exact R/H-to-b equivalence already verified for
arbitrary b-closed subsets, with **domain reflection**.

Consequently the unique countable ordered b-lift theorem yields
a unique countable ordered R/H-lift for every strictly increasing
birth-level map \(h\), with

\[
  \operatorname{range}(f_h)
   =\{v : \sigma(v)\subseteq\operatorname{range}(h)\}.
\]

The hypotheses explicitly include preservation of the
birth-level preorder; this note does **not** assert that this
preorder is definable from the reduct of the published
functional language. The result is stated for exactly the
expanded ordered embedding notion tested in the finite
R/H uniqueness theorem.

## Adversarial referee panel — internal mathematical checks

**1. Infinite source.** The closed-source b/R/H theorem
permits arbitrary, possibly infinite sets. The whole
birth carrier is b-closed. No unjustified passage from
finite subsets to a new infinite operation is made.

**2. Source subtype.** The original theorem is stated
on the subtype of a literal closed set. For \(X=M\),
this subtype is naturally the whole carrier. The proof
uses the restriction of \(f\) to that subtype, without
introducing new vertices or an isomorphic copy.

**3. Extension of the map.** The technical extension
of the subtype map by the identity outside \(X\) is
exactly \(f\), because \(X=M\). No assumptions on
the empty complement are needed.

**4. Exact b-values.** Image equality must be onto
the complete target auxiliary b-value. Preservation
of the immediate old-neighbour set or root-set
alone is not sufficient.

**5. Partial H.** Both H-value transport and
reflection of its domain are part of the theorem.
The latter is not dispensable when identifying
arbitrary R/H embeddings with b-embeddings.

**6. Inducedness.** Adjacency and nonadjacency are
reflected, not merely preserved, as in the
manuscript's embedding notion.

**7. Birth preorder.** The equivalence uses the
reflected birth-level preorder and canonical
birth order. Removing this hypothesis would
require a new proof of its intrinsic definability
in the corresponding reduct.

**8. Finite uniqueness.** Unconditional countable
existence and uniqueness depend on Track B's
already merged finite arbitrary-embedding
uniqueness theorem, not on a new uniqueness axiom.

**9. Ramsey-space boundary.** A unique global
functional lift with the correct complete-support
range does not by itself identify the finite
approximation maps and topology with those of
the synthetic supported Ellentuck space.

**10. Proof trust.** These are separate internal
mathematical challenge roles, not independent
human referees. Until the exact-head Lean build
and its three standard-axiom audits pass,
the new global R/H statement remains
submitted but uncertified.

The manuscript and Section 6 validation markers are unchanged.
