# Track C — bounded global d-closure (14 November 2026)

**Scope:** \`The-big-Hrushovski\`, Section 2, Lemma \`lem:CF-bounded-dclosure\` at manuscript main \`4acef8fd\`. Manuscript itself marks this as an English proof without an exact Lean theorem. This work concerns the plain graph \(d\)-closure, not the enumeration-generated unary closure, \(R,H\), or successor-\(d\)-closure.

**State:** draft mathematical and Lean proof, pending exact-head compile, \`#print axioms\`, full CI and source-to-statement audit. Do not promote the manuscript's validation marker before these checks.

## The argument

Let \(d\) be any finite submodular predimension on a (possibly uncountable) carrier. For \(s\subseteq c\), let \(H_c(s)\) be the existing least finite \(d\)-closed hull within the finite ambient set \(c\). The finite intersection/restriction lemma gives \(c\subseteq u\Rightarrow H_c(s)\subseteq H_u(s)\).

Suppose these hulls all have cardinality less than a fixed natural \(K\). Among their cardinalities, choose the largest: this requires only the finite set of possible numbers \(0,\ldots,K-1\), not a finite set of ambient supersets. Let \(h=H_c(s)\) realize the maximum. If \(h\) were not globally \(d\)-closed, there would be a finite \(t\supsetneq h\) with \(d(t)\leq d(h)\). In \(u=c\cup t\), the new hull \(H_u(s)\) contains \(h\). Equality would make \(h\) \(d\)-closed in \(u\), contradicting the witness \(t\); strict containment contradicts maximal cardinality. Thus \(h\) is globally \(d\)-closed. Restrict any other globally closed \(t\supseteq s\) to \(t\cap c\) and use finite leastness to prove \(h\subseteq t\).

For a graph \(G\) satisfying \(F(|u|)\leq\delta_G(u)\) for every finite \(u\), the previously verified finite-hull estimate gives \(F(|H_c(s)|)\leq 2|s|\). If \(F:\mathbb N\to\mathbb R\) is monotone and unbounded, put \(K=\min\{n:F(n)>2|s|\}\). Then every \(H_c(s)\) has cardinality \(<K\), proving the exact bound \(|h|\leq K-1=F^{\leftarrow}(2|s|)\).

This avoids the alternative minimiser-union construction of the manuscript, and needs neither countable exhaustion nor an already known global closure.

## Role-separated adversarial referees

These are logical review roles, not independent human referees.

**R1 — No circular finite exhaustion:** In particular, the proof must not assume \`DClosedChain\` or a globally closed finite cover, because the manuscript's bounded-hull lemma is used to justify finite closures before the special birth tower has been built. The only input is the finite-hull construction and the growth inequality.

**R2 — The correct strict relation:** \`d.IsGloballyDClosed h\` quantifies over every proper finite superset of \(h\), and the failure witness has \(d(t)\leq d(h)\). Weak self-sufficiency is insufficient.

**R3 — Ambient monotonicity:** The key step is \(H_c(s)\subseteq H_u(s)\) for \(c\subseteq u\), using the finite restriction of a \(d\)-closed set to its intersection with \(c\). The opposite containment is false in general.

**R4 — Attainment of maximal size:** There are infinitely many possible finite ambient graphs/subsets, so one must maximize over the finite *set of possible sizes*, not take the maximum of an infinite family of finite sets. Each chosen size must have an actual finite-ambient witness.

**R5 — Exact inverse on a plateau:** \(K-1\) is the largest integer with \(F(n)\leq 2|s|\) when \(F(0)=0\). The proof must not replace the monotone inverse with a strict inverse, or use the wider \(F^\leftarrow(2(|s|+1))\) required for a minimal local extension.

**R6 — Empty set and arbitrary carrier:** The statements allow \(s=\varnothing\) and do not require \(V\) to be countable. Empty \(d\)-closure need not itself be empty without the independent class assumption that \(\varnothing\leq_d B\) for all finite \(C_F\)-members.

**R7 — Separation from named closures:** This theorem does not show \(H(R(v))=C(v)\), the equivalence of \((b)\) and \((R,H)\) embeddings, or any Ramsey conclusion. It cannot certify those markers.

## Checks

The new dedicated workflow compiles \`CFGlobalBoundedDClosedHull\`, checks the five new declarations with \`#print axioms\` and performs a no-placeholder scan. The full Lean workflow also imports \`CheckAxiomsCFTrackCGlobalBoundedHull.lean\` through its existing \`CheckAxioms*.lean\` discovery. Keep this PR a draft until exact-head checks pass; no manuscript TeX changes are included.
