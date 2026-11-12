# Track A: canonical values under the fair birth index — adversarial review

12 November 2026. Seven internal adversarial referee roles; these are mathematical failure-mode analyses, not independent human referees.

**Precise scope:** A finite fair prefix Q_n has an arbitrary canonical component index κ on the *literal induced graph* of Q_n. Assume that for every u∈Q_n the entire unary value C(u), as a finite set of original vertices, equals the image of the κ-canonical full value under the subtype inclusion. Then the same literal equality holds for the explicit birth index β supplied by Track A #419.

1. **Finite witness reviewer:** The hypothesis supplies a canonical finite presentation of the literal Q_n; merely knowing that Q_n is C-closed is not by itself a presentation. The next separate Lean lemma must build this witness from cofinal finite stages and exact closed restriction.
2. **Class reviewer:** In every finite canonical index, equality of index fibres is equivalent to equality of entire canonical values. Injectivity of the subtype inclusion transports equality of complete C-values back to equality of finite canonical sets. It is not enough to compare cardinalities.
3. **Birth reviewer:** New β-fibres are exactly C-value classes by #419, not numerical vertex order. This is valid for every n, including 0 and stages with no vertices.
4. **Strict dependency reviewer:** If v belongs to an old canonical value of u and κ(v) differs from κ(u), then C(v)≠C(u). Because its full C-value equals the image of the old value, v is a true strict lower dependency and β(v)<β(u). No reverse inclusion is smuggled in.
5. **Graph orientation reviewer:** Reuse the already kernel-checked `canonicalValue_eq_of_lower_respecting_order` from #418, which handles cross-component edges and does not impose order on incomparable components.
6. **Full function reviewer:** The output equality is between *entire finite sets of original vertices*: image of the β-canonical value equals C(u). Weak inclusion, direct old-neighbour equality, or graph reduct isomorphism would not suffice.
7. **Trust reviewer:** Dedicated exact-head Lean source build, standard axiom audit, placeholder scan, exhaustive birth-index and finite chronological-reordering regressions, and repository-wide integration are necessary before merge. A passing conditional lemma is not yet the unconditional enumeration theorem, nor the uniform within-component ordered representative convention.

Next step: construct, for the literal Q_n, the required canonical comparison index by restricting a cofinal finite canonical stage. Reuse `canonicalValue_restrict_image` and `canonicalValue_restrict_minimalSteps` rather than re-proving reachability; the finite witness exists because each Q_n is C-closed. Avoid converting to an arbitrary isomorphic carrier unless necessary.
