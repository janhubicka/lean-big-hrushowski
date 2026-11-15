# Track E: actual ordered functional \(\omega\)-level Ellentuck space

14 November 2026. This is the last **point-space transport**
step in the \(\omega\)-level part of the big Hrushovski paper.
It is stacked on the pinned abstract SupportedEllentuck library
(PR #562) and the concrete actual ordered R/H embedding-action
recognition (PR #542, with prerequisites #516 and #494).

## The actual theorem

Let \(V\) be the original countable \(C_F\) birth carrier.
Its named expansion carries the induced graph, canonical
birth order, birth-level preorder, complete set-valued
\(R\), and the **partial** set-valued function \(H\).
Assume every birth level contains an actual empty-support
request, so there is a vertex \(z_n\) whose complete
generated support consists of exactly \(\{n\}\).

The preceding concrete work establishes that **every**
embedding of this named expansion induces a unique
strictly increasing birth-level action \(h:\omega\to\omega\),
and that its range is

\[
  U[h[\omega]]
   =\{v\in V:\sigma(v)\subseteq h[\omega]\}.
\]

The new module defines the actual copy-domain type as
the subtype of vertex subsets which are ranges of
these genuine functional embeddings. It constructs
a literal, identity-on-vertex-sets equivalence with
the already verified SupportedEllentuck copy-domain
type, using no additional Ramsey axiom.

Transporting the library's approximation system across
this equivalence gives:

- refinement order **equal to actual domain inclusion**;
- approximations **equal to the first \(n\) image levels**;
- a published A.1–A.4 Ramsey-space structure;
- Tychonoff closedness of the **complete approximation-code
  image**, not merely of the product family of all supported
  vertex subsets;
- the textbook Ellentuck theorem for the actual ordered
  partial R/H **copy-domain** space.

A further statement specializes the result to the
paper's real-growth assumptions (monotonicity and
unboundedness, finite free joins, closed empty base,
and singleton admissibility). The empty-support
request witness is discharged explicitly by a theorem
already in the repository.

This is *not* yet a claim about an unnamed reduct or
a different \(R_F\) rational-level presentation.

## Adversarial mathematical referee panel

**1. Correct actual point type.** Each point is a literal
subset \(D\subseteq V\) realized as the range of a genuine
ordered R/H embedding, not an arbitrary supported set
and not an abstractly isomorphic countable structure.

**2. No assumed level action.** The actual-copy definition
does not require the map \(h\) as extra input.
The unique increasing \(h\) follows from the named
birth-level preorder and a representative on every level,
as formalized in PR #542.

**3. Partial functional language.** The earlier global
b/R/H equivalence preserves \(R(v)\), every *defined*
\(H(S)\), and reflects the domain of the partial H.
Using only complete b-closures would not justify the
claim about the actual manuscript's functional language.

**4. Finite supports.** The domain \(U[S]\) depends on
\(\sigma(v)\), the levels of the **entire generated**
b-closure of \(v\); it is not determined merely by the
birth level of \(v\).

**5. Level-set witnesses.** The actual empty-support
request may create a multi-vertex block. The chosen
witness has singleton-*level* support \(\{n\}\).
This suffices to recover the increasing enumeration
and make domain-to-level decoding injective.

**6. Exact order.** The equivalence is identity on the
vertex subset, so the transferred refinement order
is literally inclusion. A bare bijection of arbitrary
copy labels would not justify this equality.

**7. Exact approximations.** The transported finite
approximations are the first \(n\) elements of the
level enumeration. The independent stage-image
calculation in PR #549 checks that these are the
levels represented by the actual image of the first
\(n\) birth stages. The direct stage-image theorem
requires its own verification before use.

**8. A.1–A.4.** The imported Ramsey-space theorem was
proved using the published-axiom constructor. Here its
structure is transported through an explicit equivalence
of *points* which also preserves the approximation
system, rather than merely transferring the final
Ramsey conclusion by analogy.

**9. Tychonoff topology.** Approximation-code closedness
is inherited by reindexing. This does not automatically
prove that the product topology on all Boolean
characteristic functions of copy domains agrees with
the transported metric topology. The finite-support
continuity and singleton-level witness lemmas provide
the components of that further comparison.

**10. Honest boundary of the manuscript.** The theorem
concerns the named ordered \(R,H\) expansion and its
\(\omega\)-level copy domains. It neither verifies
the \(\mathcal R_0\) nor the rational
\(\mathcal R_F\) space. Nor does it silently promote
the stronger statement that the **natural** topology
on copy domains is exactly the metric approximation
topology; that assertion should be established and
audited separately.

**11. Dependency integrity.** The Ramsey-space library
is imported from the pinned commit
\`0a585fc01894c63381451cdb38c38a9f31e4a7a7\`
under the same Lean/Mathlib revision as the Hrushovski
repository. This PR does not modify any of the
abstract Ramsey-space proofs.

**12. Trust.** These are independent internal
mathematical challenges, *not* external referee
reports. The new results are unverified until an
exact-head Lean build, eight axiom endpoints,
placeholder scan and upstream CI gates pass.

## Remaining integration obligations

1. Complete exact-head CI for all prerequisite PRs.
2. Verify that the natural product topology of genuine
   copy domains agrees with the finite-approximation
   metric topology; use already checked finite-character
   continuity and singleton-level witnesses.
3. Audit the independent first-\(n\) actual birth-stage
   image lemma before identifying the two literal
   presentations of finite approximations in prose.
4. Only then consider a green validation marker for
   the \(\mathcal R_\omega\) clause of Section 6.
   The other two clauses remain separate projects.

The manuscript has not been modified by this branch.
