# Track E: recovering the birth-level action

14 November 2026. The manuscript names the birth-level preorder
in the ordered functional expansion. Under its assumption that
every birth level contains an empty-support request, **any**
embedding of this named expansion induces a strictly increasing
map of birth levels; it is not necessary to assume such a map
in advance.

If \(z_n\) is any actual vertex born at level \(n\), let
\(h_f(n)\) be the birth level of \(f(z_n)\). Preservation and
reflection of the birth-level preorder show first that this
does not depend on the representative, and then that
\(n<m\) implies \(h_f(n)<h_f(m)\). Thus

\[
  \pi(f(v))=h_f(\pi(v))
\]

for every vertex. In particular, under the explicit level
witness hypothesis, the "has strictly increasing level action"
condition can be removed from the definition of a genuine
ordered \((R,H)\) self-embedding.

This is the missing **level-action recognition** lemma for
the \(\omega\)-level space. The result does not apply to
the reduct without the named birth-level preorder.


## Consequence for actual copy domains

The new \`allOrderedRHCopyDomains_eq_supported\` theorem
combines automatic level-action recognition with the unique
countable R/H-lifting and exact-range theorems:

\[
\{\operatorname{range}(f): f\text{ is any embedding of the
named ordered }(R,H)\text{ structure}\}
=
\{U[\operatorname{range}(h)]: h:\omega\to\omega
\text{ strictly increasing}\}.
\]

Unlike the earlier conditional family equality in PR #518,
this statement imposes **no prior level-action condition on the
embeddings being classified**. The same explicit real-stage
witness hypothesis is essential. It still does not construct
or check the finite-approximation map.

## Adversarial mathematical checks

1. **Actual witnesses.** The representatives are genuine birth
   vertices, obtained from a request with empty named support
   at each level. Existence follows from a separate theorem
   under the paper's real-growth hypotheses; no dummy
   vertices are introduced.
2. **Representative independence.** Equal source levels give
   mutual preorder comparability, hence equality of target
   levels. The proof never requires the chosen representative
   to have the same finite request tag as an arbitrary vertex.
3. **Strictness.** If images of two different levels coincided,
   target comparability in the reverse direction would reflect
   to a forbidden reverse source comparison.
4. **Order language.** Birth-level preorder and canonical
   birth order are kept distinct. The former determines the
   action, while both are preserved by the embedding.
5. **Partial functions.** The \((R,H)\) predicate still
   requires all defined \(H(S)\) values and reflection
   of the domain on which \(H\) is defined.
6. **Empty levels.** The lemma does not conclude a total
   birth-level map when some level has no vertex; the witness
   hypothesis is essential for the statement as written.
7. **Topological boundary.** Level-action recognition does
   not yet identify the finite approximation maps or prove
   that their approximation-code image is closed.
8. **Verification.** These are internal adversarial
   mathematical checks, not independent external referees.
   Seven exact axiom endpoints and the dedicated Lean build
   must pass before the theorem can be certified.

No manuscript validation marker is promoted.
