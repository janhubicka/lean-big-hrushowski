# Track A: adversarial audit of the countable one-component step

Date: 8 November 2026. This is an internal, role-separated
mathematical audit, not an external referee report. Exact Lean
kernel verification on this branch remains pending.

## New theorem

Suppose a graph `N` on the original vertex set `ℕ` admits
cofinal finite canonical C₀ stages whose **full complete unary
values** agree exactly with a finite-valued function `C`.
If finite sets `Q⊆Z` are both closed under `C` and

`∀ y, y ∈ Z \ Q ↔ C y = C x`,

then `N.toPredimension.IsMinimalStrongStep Q Z`.
This is a conclusion about the **original countable graph**, not a
statement only about a particular finite stage.

## Referee A: exact containment of the chosen component

From the equivalence at y=x, reflexive equality forces
`x∈Z\Q`. Thus x is in Z, not Q, without a separate
hypothesis. Cofinality gives a finite canonical stage containing
all of Z and thus containing x. The proof never assumes that the
stage is globally strong.

## Referee B: source presentation has empty slots

The finite canonical-stage certificate has a component index
`κ : {v // v∈stage n} → Fin m` and, at each level,
either equality of old cuts or a minimal strong step. The
nested finite theorem consumes this **exact disjunction**;
it does not strengthen it silently to “all steps nonempty.”

## Referee C: complete values, not component ranks

For vertices u and xt in the stage subtype, the equality
`C u.val = C xt.val` is equivalent to equality of the
`canonicalValue` Finsets, because both complete values become
literally equal after image along the injective `Subtype.val`.
The existing certified
`canonicalValue_eq_iff_index_eq` then equates their component
indices. In particular, `Zt\Qt` is **exactly one whole
component**, with neither missing nor extra subtype vertices.
No chronological rank alignment or distinguished generating point
is used.

## Referee D: full closedness survives stage restriction

Define `Qt` and `Zt` as the entire preimages of Q and Z in
the chosen finite stage subtype. Their exact images are Q and Z.
Because their ambient C values are exact images of finite
`canonicalValue` sets, the closure of Qt and Zt under the
canonical operation follows from closure under **all** C values,
not from adjacency to old neighbours alone.

## Referee E: predimension transport is genuinely bidirectional

The induced graph on the stage subtype has the same edges AND
nonedges under the literal injective inclusion. The previously
certified `minimalStrongStep_image_iff` transfers the actual
minimal strong step from the subtype to N with exactly the
same finite sets Q and Z. In particular, we do not merely
infer global strongness and then assume minimality.

## Referee F: independent finite counterexample search

The parent PR's exhaustive small-case falsification covers all
simple graphs of ≤4 vertices, 1,438 valid canonical index
presentations, and 14,859 closed pairs differing by one component.
The new proof additionally checks the literal stage-subtype and
complete-value transport. Finite regression is diagnostic only;
the exact countable Lean theorem must compile and its axiom
dependencies must be printed and checked.

## Referee G: remaining manuscript gap

This theorem proves **conditional** minimality of a closed
single-component step in a countable canonical presentation. It
does not construct a fair order-type-ω enumeration of all
intrinsic components, prove complete-unary equality for an
enumeration, prove countable functional Fraïssé uniqueness, or
select canonical within-component ordered representatives.
Those obligations remain open, and the manuscript's full Track A
countable proposition must stay PARTIAL.
