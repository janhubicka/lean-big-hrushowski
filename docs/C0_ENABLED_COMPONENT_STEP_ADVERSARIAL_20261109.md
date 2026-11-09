# Track A: enabled intrinsic-component step — adversarial audit

Date: 9 November 2026. These are independent **internal mathematical referee roles**, not external referee reports. Verification is conditional on exact-head CI.

## Precise statement

Let N be a countable graph with cofinal exact finite canonical C₀ presentations and full finite unary values C. Write
- P(x) = {y : C(y) = C(x)} for the finite intrinsic component;
- L(x) = C(x) \ P(x) for its strict lower set.

For a **finite C-closed** set Q and x outside Q such that L(x) ⊆ Q, let Z = Q ∪ P(x). The new Lean theorem proves simultaneously:
1. Q ≤ Z is a minimal strong step in the original countable graph N;
2. Z is globally strong in N.

The file also proves the complete-unary closedness of Z, and disjointness of Q from P(x) given x ∉ Q. No new chronological order is selected.

## Referee A: full-value closure

Take y ∈ P(x). Equality C(y)=C(x) is equality of **complete** values, not equality of old-neighbour sets. Every z ∈ C(y) is either in P(x) or in L(x). In the latter case z ∈ Q by the enabledness hypothesis. Therefore Z is C-closed. A point already in Q uses closure of Q. No assumption that P(x) itself is C-closed is made.

## Referee B: disjointness is derived, not assumed

If y ∈ Q∩P(x), then C(y)=C(x) and reflexivity gives x ∈ C(y). The complete C-closedness of Q gives x∈Q, contradicting the premise. Thus Q and P(x) are disjoint. Assuming only x∉Q without closure of Q would **not** prove this.

## Referee C: the new part really is one entire class

Disjointness gives Z\Q=P(x), and the previously certified intrinsic-component lemma characterizes P(x) by C(y)=C(x) for *every* vertex y∈ℕ, including vertices outside Z. Therefore the hypothesis of the countable component-interval theorem is met literally. It is not enough to prove a subset inclusion of complete values.

## Referee D: strongness uses the correct ambient graph

The minimal strongness is inherited from the exact countable stage theorem on N, not merely from the induced graph of one finite stage. Global strongness of Z comes from the existing closed-set theorem, not from minimality of Q≤Z alone. The proof therefore preserves the distinction between **minimal strong step** and **global strong finite prefix**.

## Referee E: negative controls

If L(x)⊄Q, the union Q∪P(x) can fail to be closed. For a two-component complete closure with C(a)={a}, C(b)={a,b}, Q=∅ and x=b, P(b)={b} is not C-closed. So dropping the enabledness condition is invalid even at the purely unary level.

If Q is not closed, x∉Q need not exclude the whole P(x); disjointness would then be an extra assumption. If finite canonical stages are absent, no statement about graph predimension follows from arbitrary unary data.

## Referee F: no unsupported enumeration claim

This theorem is **one induction step**, not the existence or fairness of the sequence of enabled components. It does not prove that the smallest-priority enabled component is always available or eventually selected, that the resulting block order has type ω, or that a prescribed order within each component is available. These remain separate obligations.

## Referee G: proof trust and CI gates

The new source is BigHrushovski/C0EnabledComponentStep.lean; CheckC0EnabledComponentStep.lean audits five exact endpoints. The isolated workflow builds the module, runs the standard axiom/placeholder checks, and runs the independently corrected finite exhaustive test. The ordinary Lean workflow must also pass on the exact head. Until then the PR remains draft and no manuscript marker changes.

The parent finite and countable interval theorems were independently Lean-built and axiom-checked on corrected 9 November 2026 heads; the parent regression was amended after independently finding 2,819, rather than 2,899, whole-carrier cases.
