# Track E: instantiate the existing SupportedEllentuck library

14 November 2026. This branch reuses the existing Lean
formalization of the abstract Ellentuck theorem instead of
repeating its published A.1–A.4 or Tychonoff code-space arguments.

## Exact reusable instance

The finite support of a vertex \(v\) in the **actual** countable
\(C_F\) birth presentation is the set of levels represented
in the *whole* least b-generated closure of \(v\). For a
strictly increasing map \(h:\omega\to\omega\), put

\[
U[h[\omega]]
=\{v:\sigma(v)\subseteq h[\omega]\}.
\]

The verified empty-support-request witness theorem produces,
at every level \(n\), a vertex \(z_n\) with
\(\sigma(z_n)=\{n\}\). Consequently the actual finite support
function satisfies the exact hypotheses of
\`RamseySpace.Examples.SupportedEllentuck\` in
\`lean-ramsey-space-todorcevic\`.

The external library defines the point space as the type
of supported vertex domains arising from increasing
enumerations, with approximations given by the first \(n\)
image levels. It already supplies:

- a bijection between increasing level enumerations and
  complete-support domains, together with the literal
  order-inclusion equivalence;
- the first-\(n\) approximation identity;
- a published-axiom Ramsey space satisfying A.1–A.4;
- Tychonoff closedness of its **approximation-code image**;
- the topological Ellentuck theorem for the supported space.

This branch instantiates all these assertions with the
actual \(C_F\) support map. A final theorem specializes the
conclusion to the paper's real-growth assumptions, using
the already verified empty-support request existence.

It does **not** identify the synthetic point type with
the ranges of all embeddings of the genuine partial
\((R,H)\) language. That is the subject of the
separately staged PRs #516, #542, #518, and #549,
which must still be fully integrated and checked.

## Dependency contract

The new direct Lake dependency is pinned to the exact
commit \`0a585fc01894c63381451cdb38c38a9f31e4a7a7\`
of \`janhubicka/lean-ramsey-space-todorcevic\`.
Both projects use Lean \`v4.35.0-rc3\` and the same
Mathlib revision
\`5bd58ac291422a21f412ae354c91e7d172255a2c\`.
The Lake manifest is updated explicitly; no other
dependency or theorem statement is changed.

## Role-separated adversarial mathematical audit

**1. Finite support.** The support map is not the vertex's
own birth level. It is the set of all levels of the
complete generated closure. This makes the support-domain
sets closed under the entire actual b-function.

**2. Singleton level witnesses.** The statement requires
\(\sigma(z_n)=\{n\}\), not a singleton-vertex block.
An empty old-support request may have several fresh
vertices and still provides the required witness.

**3. Exact source carrier.** The level witness and support
function refer to the original C_F birth vertex type.
No extra dummy vertices or abstractly isomorphic
renamed copy are used.

**4. Order versus approximation.** Point-set inclusion is
the order on supported domains. The first-\(n\) levels
are an *additional, exact finite approximation map*;
an order isomorphism by itself is not sufficient for
a Ramsey-space theorem.

**5. Tychonoff topology.** Closedness is of the space of
full approximation codes, not merely the previously
proved closed family of all complete-support domains
in the product \(2^V\). It is inherited from the
existing classical Ellentuck presentation under
an exact point equivalence.

**6. Published axioms.** The library's A.1–A.4 and
Ellentuck conclusions are imported, not reconstructed
from a successor-tree or Milliken theorem without
checking the approximation map.

**7. Real-growth hypotheses.** The empty-support
request at each stage follows only from explicitly
listed growth/free-join/empty-base and singleton
admissibility assumptions; it is not universally
true for arbitrary numerical parameters F,K.

**8. Dependency stability.** A pinned Lean/Mathlib
version avoids accidentally building against a
different mathematical API. Both Lake files must
be checked in the same exact-head workflow.

**9. Actual copy-space boundary.** The point space
here consists of synthetic supported domains.
The identifications with all genuine ordered
partial (R,H) self-embeddings, their first-n image
levels, and the natural product topology require
the separate concrete PRs and their exact Lean checks.
In particular no Section 6 green marker follows
from this theorem alone.

**10. Verification trust.** These are distinct internal
mathematical challenge roles, not independently
recruited human referees. No kernel verification
is claimed until this branch's exact-head Lean
build, eight axiom endpoints, dependency-pin check,
and placeholder scanner pass.

No manuscript validation marker is changed by this branch.
