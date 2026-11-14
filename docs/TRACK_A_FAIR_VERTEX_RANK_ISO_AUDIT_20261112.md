# Track A — explicit order-type ω rank map: adversarial audit

12 November 2026. Seven independent **internal review roles**, not external human referee reports.

Given the fair component chronology and any injective local key within each component, let r(x) be the cardinality of the finite set of predecessors of x. The proposed theorem proves r is a strict order-preserving bijection from all original vertices ℕ onto usual ℕ. It thus upgrades the previous strict-total/finite-predecessor/no-greatest interface to an **explicit order equivalence**. The actual chosen uniform local ordering is still a separate Track D obligation.

1. **Rank monotonicity/referee.** If x precedes y, then every predecessor of x also precedes y, while x precedes y but cannot precede itself. Thus Pred(x) is a proper subset of Pred(y) and its cardinal is strictly smaller. Strict totality is not needed here.
2. **Injectivity/referee.** Rank injectivity uses strict totality and therefore requires local-key injectivity on each birth component. Without this hypothesis two distinct tied vertices could have the same predecessor sets and the same rank.
3. **No skipped ranks/referee.** Pred(y) contains exactly r(y) vertices. Their ranks are distinct and all below r(y), so the image is precisely Finset.range r(y). This is established via finite cardinality and the existing `Finset.card_image_of_injective`, not assumed from the conclusion.
4. **Surjectivity/referee.** Rank zero is attained at vertex 0 or one of its finite predecessors. If k is attained at x, choose y after x (no greatest vertex). Then r(y)>k; either r(y)=k+1 or the predecessor image lemma produces a vertex of rank k+1. This does not use a circular assumption of surjectivity.
5. **Finite/infinite-referee.** The predecessor-image lemma also holds on finite orders. Surjectivity to all ℕ uses the genuinely infinite-carrier theorem `fairVertexBefore_no_greatest`, not a finite regression.
6. **Presentation-referee.** A bijection x↦r(x) realizes order type ω while allowing arbitrary componentwise injective local numeric keys. The raw numeric-label choice is an instance but need NOT be the uniform chosen local ordered representative in the Ramsey expansion. No non-precompact-Ramsey or BRD theorem follows.
7. **Kernel/referee.** Nine exact axiom endpoints, isolated Lean kernel check, full repository CI, placeholder scan, and finite exhaustive falsification of rank comparison/predecessor image/bijection are required before merge. Keep the manuscript PARTIAL until the *chosen* local orders and functional Fraïssé conditions are established.

The result reuses merged Track A fair component birth proofs and the parent draft #439; neither a new closure calculus nor a countable sorting axiom is introduced.
