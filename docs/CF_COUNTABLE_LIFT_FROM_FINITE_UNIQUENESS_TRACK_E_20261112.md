# Track E: countable lifts and exact ranges from finite uniqueness

12 November 2026. This is a **conditional** result: the sole
unproved mathematical hypothesis is uniqueness of finite
ordered b-embeddings on complete one-generated closures when
the birth level of every source vertex has the same image.
The purpose is to show that neither countable coherence nor
countable existence should remain an additional independent
obstacle once that finite rigidity statement is established.

## The theorem

Let \(F,K\) be the parameters of the actual countable
\(\mathcal C_F\) birth construction. Let
\(h:\mathbb N\to\mathbb N\) be strictly increasing. Assume:

> For each vertex \(v\), any two genuine ordered finite
> b-embeddings of its complete one-generated closure \(C(v)\)
> which agree on target birth levels of all its vertices
> are identical.

Then there is a **unique** global ordered b-embedding \(f_h\)
of the countable birth carrier with birth-level action \(h\).
It is injective, induces the complete graph, preserves exact
complete b-values, the birth-level preorder, and the canonical
order. Its range is exactly

\[
  \operatorname{range}(f_h)
   =\{v:\sigma(v)\subseteq\operatorname{range}(h)\}.
\]

Here \(\sigma(v)\) consists of all levels represented in the
full generated b-closure \(C(v)\).

The theorem does NOT prove the stated finite uniqueness
hypothesis. Nor does it yet identify the global b-language
with all embeddings of the partial \((R,H)\) language, or
formalize the Ramsey-space approximation system.

## Proof structure

**A. Finite restriction.** If \(s\subseteq t\) are finite
vertex sets with \(s\) b-closed, every complete b-embedding
of \(t\) restricts to a complete b-embedding of \(s\).
The key point is that the restricted finite b-value of a
vertex in \(s\), viewed within \(t\), contains **exactly the
same vertices**: it is the full ambient b-value.
No closedness of the larger set \(t\) is needed.

**B. Local uniqueness implies stage uniqueness.** For
any vertex \(v\in U_n\), its complete generated closure
\(C(v)\) is contained in \(U_n\), which is b-closed.
Two embeddings of \(U_n\) agreeing on birth levels
restrict to two embeddings of \(C(v)\). By the given
finite uniqueness, they agree at \(v\); since \(v\)
was arbitrary, the maps of \(U_n\) agree everywhere.

**C. Choose finite lifts.** For every \(U_n\), apply
Track B's finite prescribed ordered lift theorem to
the restriction of \(h\) to the represented birth
levels of \(U_n\). The source may have missing levels,
and \(U_0\) may be empty. Choose a witness \(e_n\).

**D. Automatic coherence.** Restrict \(e_m\) to
\(U_n\) for \(n\le m\). By A it is still an embedding
and by the prescribed birth-level equations it has
the same level action as \(e_n\). By B these two
maps are equal. Thus the chosen stage maps form a
coherent family; no extra coherence axiom is needed.

**E. Global lift.** Apply the separate Track E gluing
lemma from PR #487. The resulting map is a
global ordered b-embedding whose level action
is exactly \(h\).

**F. Range and uniqueness.** Use the conditional
range theorem of PR #461, which has the same
finite uniqueness hypothesis, to identify
\(\operatorname{range}(f_h)\).
For uniqueness of global maps, restrict each
candidate to \(C(v)\), apply the finite uniqueness
hypothesis, and conclude equality at every \(v\).

## Role-separated adversarial review

1. **Full finite function values.** Restriction is only
   valid for b-closed \(s\). We prove explicitly that
   the restricted value within the larger source equals
   the entire ambient b-value; neither an inclusion
   nor old-neighbour preservation suffices.
2. **No hidden closure of t.** The restriction lemma
   does not assume \(t\) is b-closed. Only the original
   finite map's exact value equation and closure
   of the smaller source are used.
3. **Gaps and the empty stage.** Strictly increasing
   \(h\) restricts to the represented levels of
   \(U_n\), even with gaps. No requirement is made
   that an arbitrary increasing inverse is defined
   on all natural-number coordinates.
4. **Stage uniqueness.** The hypothesis is applied to
   all of \(C(v)\), not merely to \(v\). It gives
   stagewise uniqueness only after the hereditary
   restriction statement is established.
5. **No circular coherence.** The choice of every
   finite lift is made before proving coherence.
   Restriction plus finite uniqueness forces agreement
   on overlaps. No continuity or limit map is
   postulated to establish finite agreement.
6. **Countable gluing.** Complete b-values lie within
   finite birth stages; their images are transported
   by the corresponding finite embedding. Pairwise
   graph and order properties are decided on a
   common finite stage.
7. **Exact range.** A global embedding having the
   correct level action does not automatically
   imply the reverse range inclusion. We explicitly
   invoke PR #461, which itself needs the same
   still-unproved finite uniqueness theorem.
8. **Language boundary.** A result for the auxiliary
   ordered b-language must not be promoted as a
   classification of all \((R,H)\)-embeddings until
   equivalence of the countable embedding notions
   is instantiated and validated, including the
   partial domain of \(H\).
9. **Topology boundary.** Even existence and
   uniqueness of global lifts plus the range formula
   do not by themselves verify that the actual finite
   approximations match the first represented levels,
   or that the relevant approximation code image is
   Tychonoff closed. These are separate Track E
   identifications needed for Ellentuck.
10. **Proof trust.** The panel consists of internal
   adversarial mathematical roles, not separately
   recruited human referees. Exact-head Lean
   compilation, standard axiom inspection and a
   placeholder scan are required before declaring
   any theorem certified.

## Verification and integration

The new modules are:

- HrushovskiEllentuckFiniteRestriction
- HrushovskiEllentuckCountableLiftFromFiniteUniqueness

They deliberately reuse the predicates and lemmas
introduced in PRs #461 and #487. This branch is
stacked above those PRs rather than introducing
duplicate finite-embedding definitions or changing
the manuscript.

It has a dedicated audit with eleven exact
#print axioms endpoints. No Section 6 validation
marker is changed.

**Pending theorem:** prove the actual finite uniqueness
on complete one-generated closures. That proof should
come from the Track B programme of comparing named
supports, fresh-block sizes, ordered adjacency matrices,
and canonical ordinals.
