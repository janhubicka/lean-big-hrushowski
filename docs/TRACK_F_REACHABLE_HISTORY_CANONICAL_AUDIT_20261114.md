# Track F — reachable tagged histories produce canonical SCC assignments

14 November 2026. Stacked on the tagged-history inverse (#543)
and canonical-step preservation (#547). No manuscript or
validation-marker changes.

## Exact finite theorem proposed for Lean certification

Fix a legal ranking \(r\) of the actual SCCs. A reachable history
of length \(n\) is formed by repeatedly choosing an actual tagged
internal order for the SCC of rank \(i<n\), with the complete
canonical directed-adjacency-code test checked at each stage.

The theorem \`reachableTaggedHistory_canonical_prior\` proves by
induction that *every* SCC of rank less than \(n\) passes its full
canonical test in the complete component-order assignment executed
from that history. The base case is vacuous; the induction step
unpacks the new dependent tag, applies the canonical next-choice
membership predicate at the current SCC, then transports all
previous component tests across the later SCC update using the
rank-prefix locality established in #492 and repackaged in #547.

The specialization at the full number of SCCs is

\[
  h\in H_m(r)\quad\Longrightarrow\quad
  \operatorname{IsCanonicalComponentAssignment}
  (r,\operatorname{ordersFromReverseHistory}(h)).
\]

The result concerns *literal* orders of the original labelled
components, not isomorphism classes. It is **one direction** of
the finite global history/assignment bijection. The converse
and injectivity remain open until separately checked.

## Adversarial panel — independent mathematical challenge roles

1. **Rank referee.** The inserted tag has component
   \(r^{-1}(n)\), never an arbitrary SCC. Its rank is exactly
   the preceding history length; there is no off-by-one stage.
2. **Reachability referee.** The induction uses the actual
   \`reachableHistories\` recursion, not arbitrary lists of
   tagged choices. Nonmembers of the next-choice set must not
   be accepted.
3. **Persistence referee.** The canonicality of an earlier
   component survives the new update only because the
   ranking is legal and the complete successor closure lies
   in the earlier prefix. A later SCC order must not modify
   any old complete adjacency-code entry.
4. **Full code referee.** Each stage tests the entire induced
   directed adjacency matrix on \(C_B\), including nonedges,
   not just the order or adjacency within the top SCC B.
5. **Dependent-carrier referee.** Recovering the tag at
   rank \(n\) must preserve its dependent carrier
   \(\mathrm{Fin}(|B|)\simeq B\). Equality of numerical sizes
   does not identify different actual SCCs.
6. **Boundary referee.** For the empty component set, the
   reachable history is empty and the canonicality conclusion
   is vacuous; no hidden positivity assumption is allowed.
7. **Certification referee.** Require exact-head Lean build,
   named kernel-axiom audit and placeholder scan, plus
   independent exhaustive finite checks. This panel is
   role-separated internal verification, not external human
   refereeing.

## Independent finite regression

For every orientation with at most four vertices, every legal
component ranking, and all reachable partial canonical
assignments, the independent script checks every previously
selected SCC's full local canonical predicate after each update.
The test is sensitive to the *order* of the tagged choices and
does not identify SCCs which merely have isomorphic induced
orientations.

## Remaining direction

Given a canonical *complete* assignment \(\mathbf e\), construct
the tagged rank-prefix history of its actual SCC orders (PR #543).
By induction its stage-\(n\) prefix is reachable: the previous
prefix matches \(\mathbf e\) on all components of rank below \(n\),
and after adding the next SCC it agrees through rank \(n\).
Canonical rank-prefix locality (#492) transfers the full
canonicality of \(\mathbf e\) to the partial assignment. This
supplies the next-choice membership proof.

Then prove that the complete history and assignment maps are
inverse on the restricted sets, and combine the unconditional
reachable-history count (#533) with the already certified
canonical-data count (#488). No infinite Ramsey theorem follows
from this finite count without a separate upper/lower-bound
argument and exact agreement with the manuscript expansion.
