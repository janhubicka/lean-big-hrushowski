# Track C — exact strong age and manuscript correspondence (13 November 2026)

**Verification state:** proposed Lean theorem on this branch; do not call it kernel-verified until the exact-head dedicated build, axiom audit and full Lean CI succeed. No manuscript validation marker is changed by this PR.

## Printed statement and formal endpoints

Manuscript: *The Big Hrushovski*, v52, Section 3.2, Lemma 3.14, printed pages 16–17. It claims (i) each finite stage and each extension level has finitely many blocks and (ii) the graph reduct of the canonical union \\(M_F^\\dagger\\) is isomorphic to the strong Fraïssé limit \\(M_F\\).

Previously validated Lean results cover:
- stages are finite by their finite canonical catalogue/birth construction, and the literal countable graph and chain use the actual birth carrier;
- `publishedBirth_standardStrongFraisseLimitPresentation`: countably infinite enumeration, hereditary finite growth inequality, finite globally strictly \\(d\\)-closed covering chain and ordinary arbitrary-finite prescribed strong extensions;
- `publishedBirth_finiteStrongUniversality`: a globally strictly \\(d\\)-closed induced copy of every finite \\(C_F\\)-member;
- `publishedBirth_strongHomogeneous`: arbitrary finite globally strictly \\(d\\)-closed induced partial isomorphisms on the actual carrier extend pointwise to automorphisms;
- `publishedBirth_iso_standardStrongFraisseLimit`: the induced-isomorphism to every specified countable \\(M_F\\) with the ordinary strong Fraïssé limit properties.

The new `publishedBirth_exactStrongAge` combines *both directions* of the age equivalence with the strong-image requirement in one statement. It uses `GraphOn.growthSparse_image_iff` for the reverse implication; the forward implication is the already established strong universality theorem.

## Role-separated adversarial referees

These are independent **logical test roles**, not external referees.

**R1 — Printed assumptions:** \\(F : \mathbb{R}_{\ge0}\to\mathbb{R}_{\ge0}\\) has \\(F(0)=0\\), monotonicity, unboundedness, singleton class membership \\(F(1)\le2\\), empty strict base and restricted strict-free-amalgamation. Continuity in the printed statement is stronger than required for these finite results; Lean does **not** claim the class assumptions follow from monotonicity.

**R2 — Exact age, both directions:** The `age` field alone proves only \\(\operatorname{Age}(M_F^\dagger)\subseteq C_F\\). The strong universality theorem supplies the other inclusion. The iff newly exposes this essential distinction, without assuming full age in its hypotheses.

**R3 — Literal finite carriers:** The finite graph is `B : GraphOn W` for *arbitrary* finite `W`, without a `LinearOrder W` assumption. The induced injection uses the unmodified `W` and preserves/refects adjacency for every pair.

**R4 — Strict strength and no circularity:** The existence direction explicitly produces a *globally* strictly \\(d\\)-closed image inside the entire infinite birth graph. No isomorphism to a pre-existing \\(M_F\\) is used in the age equivalence. The reverse implication needs only inducedness, not closure.

**R5 — Empty/singleton boundary:** `W` may be empty. Empty strict closure is an independent published class assumption; the numerically exact singleton condition supplies infinitely many birth vertices for the full Fraïssé presentation.

**R6 — Scope and exclusions:** This proves the graph reduct's finite strong age, not the equivalence of the final functional \\(R,H\\)-embedding notions, the level-lifting lemma, the embedding monoid, the Ramsey properties, or Ellentuck results. No validation markers for these further claims may be upgraded.

## Verification gate

Run exact-head dedicated `Track C exact strong age`, full `Lean`, and `#print axioms` for `publishedBirth_exactStrongAge`. The repository-wide placeholder scan is a separate check. This file's assertions must not be advertised as newly verified before CI completes.
