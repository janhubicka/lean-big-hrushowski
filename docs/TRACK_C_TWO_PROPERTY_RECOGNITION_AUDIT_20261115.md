# Track C: remove redundant finite strict-cover assumption

**15 November 2026.** This is a mathematical and code audit of the two-property strong Fraïssé recognition theorem, submitted as a draft PR. It is **not** an external human referee report. No theorem marker should be promoted before exact-head Lean and axiom checks succeed.

## Statement and reduction

Let \(F:[0,\infty)\to[0,\infty)\) satisfy \(F(0)=0\), monotonicity, and unboundedness. Let \(G\) be a graph on a countably infinite vertex set, with (i) \(F(|s|)\le\delta_G(s)\) for every finite \(s\), and (ii) the ordinary **prescribed** finite strict \(d\)-closed extension property: every finite \(C_F\) extension \(A\le_d B\) embeds over every induced globally \(d\)-closed copy of \(A\), with induced, globally \(d\)-closed image. Under the published independent free-amalgamation, empty strict base, and singleton assumptions for \(C_F\), the actual birth graph \(M_F^\dagger\) is induced-isomorphic to \(G\).

The new observation is that no finite \(d\)-closed exhaustion of \(G\) needs to be *assumed*. The established bounded-hull theorem implies that every finite subset has a finite globally strictly \(d\)-closed hull. The exact finite-response theorem and the independently given \(\mathbb N\simeq V\) then supply all inputs to the prior strict back-and-forth identification.

The Lean theorem \`CFCoherentTower.publishedBirth_iso_of_growth_and_extensions\` quantifies over the **original** comparison carrier \(V\), not a specified independent model isomorphism. It does not assume the comparison is already isomorphic to \(M_F^\dagger\).

## Adversarial referee roles (internal logical audits)

**R1 — Missing assumption:** The bounded-hull theorem requires monotone unbounded \(F\) and the growth bound on *all* finite subsets, not just finitely many initial stages. Both are present. The new theorem retains class-level strict free joins, strict empty base, and singleton membership; it does not claim these follow from \(F\)'s growth.

**R2 — Weak versus strict:** The cover conclusion is \`IsGloballyDClosed\`, not weak self-sufficiency. Its proof is the exact finite-size stabilization theorem; no weak-strong substitution occurs. The finite extension predicate demands the same strict global image.

**R3 — Empty base:** A nonempty source \(C_F\) age alone does not imply global strict closure of the empty set. The explicit \`EmptyDClosedInGrowthClass\` assumption yields it by the separately verified \`HasFiniteFraisseData.toStrictGenericity\` step. Omitting this step would invalidate initial back-and-forth.

**R4 — Carrier and infinity:** The comparison graph is on arbitrary \(V\) but requires a genuine \`ℕ ≃ V\`. Merely \`Countable V\` is insufficient, especially if the finite age has no singleton. The canonical birth graph's infinitude still uses the independent singleton hypothesis.

**R5 — Prescribed embeddings and nonedges:** The response interface takes arbitrary finite \`W\`, a literal closed source, and a prescribed injective induced map fixing all old vertices. Its target preserves and reflects adjacency, hence nonedges. Do not replace this by one-sided graph homomorphism or existence of an unspecified copy.

**R6 — Closed covers are not an extra class assumption:** The general declaration \`finiteDClosedCovers_of_growth\` derives them from growth alone, with no finite-response hypothesis. Thus the new two-property criterion is not circular.

**R7 — Exact published domain:** Monotonicity and unboundedness on \(\mathbb R_{\ge0}\) pass to the integer cardinality restriction through the existing verified growth adapter. No continuity is used in this implication.

**R8 — Proof imports and scope:** The new theorem reuses \`CFPublishedFraisseRecognition\`, finite subtype response transport, \`CFFraisseThreeData\`, and \`CFPublishedGlobalBoundedDClosedHull\`. It states graph-level isomorphism only; it does not certify the auxiliary order, \(R,H\), finite/limit level lifts, Ramsey degrees, or Ellentuck.

## Verification gates

- Exact-head dedicated build \`Track C two-property Fraisse recognition\`.
- Full Lean workflow on the same PR head.
- Four \`#print axioms\` endpoints, restricted to \`propext\`, \`Classical.choice\`, and \`Quot.sound\`.
- Repository placeholder scan and line-by-line statement comparison.
- Only after successful checks: integrate a short note in Section 3.2 of the manuscript (or the introduction), without modifying the established proof itself.
