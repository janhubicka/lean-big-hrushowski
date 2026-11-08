# Track C — the ordinary finite strong Fraïssé extension property

This file removes the last substantial *encoding* mismatch in the
manuscript-facing C_F strong Fraïssé limit identification.

The manuscript uses arbitrary finite graphs B in C_F, finite
d-closed A≤_d B, and an induced strong embedding A→M_F.
Our Nat-countable uniqueness theorem initially takes an
interval a≤_d b inside an arbitrary Nat-graph. Those
formulations must not be silently interchanged.

## Exact new proof

`HasStandardFiniteDClosedExtensions F G` requires an induced,
globally strictly d-closed response to **every** finite
C_F diagram on an arbitrary finite vertex carrier W,
over every literally prescribed induced global strictly
d-closed map of its d-closed old subset A.

`toNatIntervals` applies it to the *literal* induced
subtype `{v : ℕ // v∈b}` of the finite Nat interval
a≤_d b. The already verified `CFDClosedFiniteSubtype`
lemmas transport full finite age membership and strict
relative closure. The old-subtype equivalence fixes
each literal old vertex; the finite extension is transported
back without losing old values, inducedness, or global
strict image closure.

`StandardStrongFraisseLimitPresentation` now packages the
**ordinary** manuscript limit data on its original carrier:
a countably infinite enumeration, full finite C_F age,
a covering finite d-closed chain, and the standard
arbitrary-finite strong extension property.
The method `toNative` derives the previously verified
Nat-interval interface without adding any assumption.

Finally `realBirth_iso_standardStrongFraisseLimit` invokes
the kernel-checked countable birth genericity theorem through
these derived properties.

## Role-separated internal adversarial panel

- **Finite-age referee:** the *whole finite endpoint* B is
  required in C_F; the infinite source M in the Nat
  interval theorem need not belong to C_F outside b.
- **Closure referee:** every finite d-closed inclusion uses
  strict predimension inequalities. Weak self-sufficiency
  is insufficient.
- **Map referee:** all old values are exactly fixed, and the
  finite maps preserve and reflect graph edges, including
  old--fresh and fresh--fresh nonedges.
- **Carrier referee:** the finite subtype has the literal
  old labels; no arbitrary total map from the whole
  infinite source is selected, even for empty stages.
- **Limit referee:** a covering strictly d-closed chain
  yields global closed covers. The comparison structure
  is not assumed isomorphic to the canonical birth graph.
- **Fraïssé referee:** the *forward* implication from the
  usual finite-source extension property to our Nat
  interval property is proved. A full logical
  equivalence in both directions is not claimed.
- **Certification referee:** exact isolated Lean build,
  `#print axioms`, placeholder scan and a later global
  integration check are required. No green manuscript
  marker is promoted before these succeed.

This is internal role-separated checking, not a panel
of independent external human reviewers. Current status:
awaiting isolated CI.
