# Track B: complete request code under arbitrary finite embeddings

12 November 2026 — candidate integrated proof, conditional on
compilation of the four supporting interfaces (#465, #466, #469,
#471). This theorem is not yet kernel-certified.

## Statement and intended proof

Let s be finite and closed under complete b-values, and let
e:s→M_F^† be injective, induced, b-value preserving, and
preserving/reflection the actual birth-level preorder and
canonical order. For every represented source request r at n
and any v=(n,r,i) in s, write e(v)=(m,t,j). Then the
**complete ordered adjacency matrix** of r equals the
complete ordered adjacency matrix of t.

All coordinates of the source local request are in s by
b-closedness. The old-source-support image is the exact
named target support, so a partial order isomorphism of the
literal old supports exists. Its pointwise image equals e
on each old coordinate. The fresh block has exactly the
same cardinality, and every source fresh ordinal is sent
to the same target request at the same numerical ordinal.
Hence both halves of the sorted local coordinate list map
exactly to those of t. The induced map preserves and
reflects every adjacency bit. The generic code-transport
theorem then gives equality of the entire ordered matrices.

## Six adversarial referee roles

1. **Named supports:** The old coordinate isomorphism is
   constructed from the actual image e[P_r]=P_t, not an
   abstract isomorphism or arbitrary global old-stage map.
2. **Pointwise accuracy:** A bare order isomorphism is NOT
   sufficient. The proof uses the pointwise equation for
   e(toVertex n u) from the supporting #466 theorem.
3. **All fresh vertices:** Complete b-closedness supplies
   every j in the source block; the #469 theorem forces
   their images to retain the same literal target request
   tag and the same ordinal value. Distinct fresh
   cardinalities are excluded using #440.
4. **All adjacency bits:** The #471 induced local map is
   an equivalence on every pair of the old-plus-fresh
   coordinate carrier. The final code theorem (#430)
   therefore includes old–old, old–fresh, fresh–fresh
   **and nonedges**. One-sided graph homomorphisms
   cannot justify it.
5. **Empty old stage and gaps:** The proof never extends
   the source's partially defined old map to all U_n,
   nor postulates any globally increasing ℕ-map.
   Empty named supports and target U_0 are admitted.
6. **Scope and certification:** This endpoint proves
   equality of source and target full adjacency matrices
   for ONE arbitrary finite embedding. To deduce
   **uniqueness between two embeddings**, compare their
   target birth levels, literal support images and
   fresh sizes, then use request-record uniqueness and
   block ordinal rigidity. The represented-level
   induction and countable monoid are still pending.
   No validation marker is promoted until exact-head
   Lean CI and the axiom/placeholder audit pass.

These are internal role-separated adversarial checks, not
independent external human referee reports.

```sh
lake build BigHrushovski.CFArbitraryFiniteLocalCode
lake env lean CheckAxiomsCFTrackBArbitraryLocalCode.lean
python3 scripts/check_no_placeholders.py
```

Dependencies: merged one-level request-code theorem #430,
arbitrary finite size #440, ordered target-support #465,
pointwise support #466, fresh-coordinate #469, and
whole-local induced map #471.
