# Track E — actual ordered R/H copy domains and level sets

13 November 2026.

## Mathematical statement

Let \(V\) be the actual countable birth carrier of
\(\mathcal C_F\), with its induced graph, canonical birth
order, birth-level preorder, and genuine partial
\((R,H)\) operations.

The previous countable lifting theorem associates to
every strictly increasing level map \(h:\omega\to\omega\)
a unique ordered functional embedding \(f_h:V\to V\),
with exact range

\[
  \operatorname{range}(f_h)
  =U[\operatorname{range}(h)]
  =\{v:\sigma(v)\subseteq \operatorname{range}(h)\}.
\]

Here \(\sigma(v)\) is the **full** finite set of levels
represented in the complete generated functional closure
of \(v\), not merely its own birth level.

This PR proves the literal equality of two sets of subsets
of \(V\):

\[
\begin{split}
&\{\operatorname{range}(f):
   f \text{ is an ordered }(R,H)\text{-embedding with}\\
&\hspace{30mm}\text{some strictly increasing level action}\}\\
&\qquad =
\{U[\operatorname{range}(h)]:h:\omega\to\omega
   \text{ strictly increasing}\}.
\end{split}
\]

The forward direction uses range equality for **every**
appropriate embedding, not just one chosen lift.
The reverse direction uses existence of the actual R/H
lift for each increasing level action.

## Order and topology

If every birth level has an empty-support request,
the existing exact singleton-level witness theorem gives

\[
U[S]\subseteq U[T]\quad\Longleftrightarrow\quad S\subseteq T.
\]

The PR applies this to \(S=\operatorname{range}(h)\)
and \(T=\operatorname{range}(k)\).
The witness hypothesis is *not* silently assumed for
arbitrary numerical parameters \(F,K\). It is already
available under the paper's real-growth/free-join
hypotheses in the verified empty-request theorem.

This PR does not yet prove that the first \(n\) image
levels of an actual functional copy yield the literal
finite approximation map of the synthetic Ellentuck
space, or that the resulting approximation-code image
is Tychonoff closed. A family of copy domains is not
itself a topological Ramsey-space proof.

## Internal adversarial referee panel

1. **Actual language.** R(v) and the partial H(S) are
   the genuine operations on the countable presentation,
   including reflection of H's domain. No surrogate
   total closure operation is substituted.
2. **Full support.** Every vertex's entire generated
   closure contributes to the range formula. Its own
   level alone is insufficient.
3. **Every embedding.** The forward implication covers
   arbitrary global ordered embeddings *with* the
   specified strictly increasing level action, not
   merely the canonical witness chosen by existence.
4. **Existence versus equality.** The reverse direction
   constructs a true global R/H embedding for each h
   by the previously proved existence-and-uniqueness
   theorem; it does not infer existence merely from
   the closedness of support domains.
5. **Named level preorder.** The language includes
   the manuscript's birth-level preorder. Arbitrary
   embeddings without a known level action are not
   yet classified in the formal theorem.
6. **Singleton witnesses.** Reflection of level-set
   inclusion requires witnesses of exact singleton
   **level** support, not singleton-vertex birth blocks.
7. **Empty and omitted levels.** Finite source cuts
   can have gaps, but the globally increasing level
   action has infinite range. The two conditions
   are not conflated.
8. **Topological scope.** Closedness of *all* complete
   support domains in \(2^V\) does not imply closedness
   of the subfamily with infinite level sets, nor
   the Ellentuck approximation-code closedness.
9. **Dependencies.** The actual R/H range theorem
   uses merged finite uniqueness and the pending
   global R/H lift, not an extra assumed uniqueness
   axiom.
10. **Trust.** These are distinct internal mathematical
    challenges, not separately recruited human
    referees. Exact-head Lean compilation, axiom
    inspection and placeholder scanning remain
    required before promotion.

No manuscript statements or validation markers are
changed in this PR.
