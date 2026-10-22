import BigHrushovski.CFClosedSourceRootOrder
import BigHrushovski.FiniteRestrictedNeighbourTransport
import BigHrushovski.FiniteRestrictedHullTransport

/-!
# Recover complete b-values from R,H on an arbitrary closed C_F source

A genuine functional embedding of a closed source substructure need
not extend to an induced self-embedding of the full countable
generic. This module imposes every graph, injectivity, level and
function-value condition only on a possibly infinite b-closed
source X. Nothing is assumed about f outside X.

Exact R(v) and defined H(S) values first recover C(v) as the
global d-hull of R(v). The top birth-level part of C(v) is the
whole block B(v), so the reflected level preorder transports
B(v) exactly. The old named support is the finite d-hull inside
C(v) of its old neighbours, whose image is computed using the
finite restricted neighbour and hull transport lemmas. Therefore
the complete auxiliary value b(v)=P_B ∪ B is preserved exactly.

This is the converse to the verified closed-source b-to-(R,H)
direction, with no global induced extension assumption.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Set difference commutes with the image of an injection
which is injective only on a finite containing set C. -/
theorem finite_image_sdiff_on
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (f : U → V) (C B : Finset U)
    (hB : B ⊆ C)
    (hf : ∀ u ∈ C, ∀ v ∈ C, f u = f v → u = v) :
    (C \ B).image f = C.image f \ B.image f := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy
    obtain ⟨huC, huNotB⟩ := Finset.mem_sdiff.mp hu
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, huC, huy⟩
    · intro hyB
      obtain ⟨v, hvB, hvy⟩ := Finset.mem_image.mp hyB
      have hvEq : v = u :=
        hf v (hB hvB) u huC (hvy.trans huy.symm)
      exact huNotB (hvEq ▸ hvB)
  · intro hy
    obtain ⟨hyC, hyNotB⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨u, huC, huy⟩ := Finset.mem_image.mp hyC
    have huNotB : u ∉ B := by
      intro huB
      exact hyNotB (Finset.mem_image.mpr ⟨u, huB, huy⟩)
    exact Finset.mem_image.mpr
      ⟨u, Finset.mem_sdiff.mpr ⟨huC, huNotB⟩, huy⟩

/-- Exact C(v)-images follow from complete R and defined H-values
only on the closed source X. Every member of R(v) belongs to X
because the source is b-closed, so H is invoked within its
legitimate partial-function domain. -/
theorem birthCValue_image_of_RHValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hR : ∀ v ∈ X,
      (birthReachableRoots F K v).image f =
        birthReachableRoots F K (f v))
    (hH : ∀ s : Finset (Vertex F K),
      (∀ r ∈ s, r ∈ X) →
      (∀ r ∈ s, IsBirthRoot F K r) →
      (birthDClosedHull F K s).image f =
        birthDClosedHull F K (s.image f))
    (v : Vertex F K) (hv : v ∈ X) :
    (birthCValue F K v).image f = birthCValue F K (f v) := by
  let C := birthCValue F K v
  let R := birthReachableRoots F K v
  have hCsubX : ∀ w ∈ C, w ∈ X :=
    generatedClosure_subset_closedSet F K X hX
      ({v} : Finset (Vertex F K)) (by
        intro u hu
        have huv : u = v := by simpa using hu
        subst u
        exact hv)
  have hRsubsetC : R ⊆ C := by
    simpa only [R, C, birthCValue, birthReachableRoots] using
      (rootsOf_subset_closed F K
        (birthGeneratedClosure F K ({v} : Finset (Vertex F K)))
        (birthGeneratedClosure_closed F K ({v} : Finset (Vertex F K))))
  have hRinX : ∀ r ∈ R, r ∈ X :=
    fun r hr => hCsubX r (hRsubsetC hr)
  have hRroots : ∀ r ∈ R, IsBirthRoot F K r :=
    reachableRoots_are_roots F K v
  have hEq : C = birthDClosedHull F K R :=
    (birthRoot_recovery F K v).symm
  calc
    C.image f = (birthDClosedHull F K R).image f :=
      congrArg (Finset.image f) hEq
    _ = birthDClosedHull F K (R.image f) :=
      hH R hRinX hRroots
    _ = birthDClosedHull F K (birthReachableRoots F K (f v)) := by
      rw [hR v hv]
    _ = birthCValue F K (f v) := birthRoot_recovery F K (f v)

/-- Exact C(v)-images and reflected level equality on X already
force the complete image of the top birth block B(v). -/
theorem birthBlockOf_image_of_CValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hC : ∀ v ∈ X,
      (birthCValue F K v).image f = birthCValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (v : Vertex F K) (hv : v ∈ X) :
    (birthBlockOf F K v).image f = birthBlockOf F K (f v) := by
  classical
  let C := birthCValue F K v
  have hCX : ∀ w ∈ C, w ∈ X :=
    generatedClosure_subset_closedSet F K X hX ({v}) (by
      intro u hu
      have huv : u = v := by simpa using hu
      subst u
      exact hv)
  have hCv : C.image f = birthCValue F K (f v) := hC v hv
  ext y
  constructor
  · intro hy
    obtain ⟨w, hwB, hwy⟩ := Finset.mem_image.mp hy
    obtain ⟨hwC, hwLevel⟩ :=
      (birthBlockOf_mem_iff F K v w).mp hwB
    have hfyC : y ∈ birthCValue F K (f v) := by
      rw [← hCv, ← hwy]
      exact Finset.mem_image.mpr ⟨w, hwC, rfl⟩
    have hfyLevel : y.1 = (f v).1 := by
      rw [← hwy]
      exact (birthLevelEq_on F K X f hLevel w v
        (hCX w hwC) hv).mp hwLevel
    exact (birthBlockOf_mem_iff F K (f v) y).mpr
      ⟨hfyC, hfyLevel⟩
  · intro hy
    obtain ⟨hyC, hyLevel⟩ :=
      (birthBlockOf_mem_iff F K (f v) y).mp hy
    have hImage : y ∈ C.image f := by
      rw [hCv]
      exact hyC
    obtain ⟨w, hwC, hwy⟩ := Finset.mem_image.mp hImage
    have hwLevel : w.1 = v.1 :=
      (birthLevelEq_on F K X f hLevel w v
        (hCX w hwC) hv).mpr (by
          rw [hwy]
          exact hyLevel)
    exact Finset.mem_image.mpr
      ⟨w, (birthBlockOf_mem_iff F K v w).mpr
        ⟨hwC, hwLevel⟩, hwy⟩

/-- Intrinsic support recovery transports exactly under induced
maps *only on a closed source X*, once C(v) and the top block
have their exact images. -/
theorem birthSupportOf_image_of_CValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hC : ∀ v ∈ X,
      (birthCValue F K v).image f = birthCValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (v : Vertex F K) (hv : v ∈ X) :
    (birthSupportOf F K v).image f =
      birthSupportOf F K (f v) := by
  classical
  let G := countableGraph F K
  let d := G.toPredimension
  let C := birthCValue F K v
  let C' := birthCValue F K (f v)
  let B := birthBlockOf F K v
  let B' := birthBlockOf F K (f v)
  let N := G.oldNeighbourSet (C \ B) B
  let N' := G.oldNeighbourSet (C' \ B') B'
  have hCX : ∀ w ∈ C, w ∈ X :=
    generatedClosure_subset_closedSet F K X hX ({v}) (by
      intro u hu
      have huv : u = v := by simpa using hu
      subst u
      exact hv)
  have hCv : C.image f = C' := hC v hv
  have hBv : B.image f = B' :=
    birthBlockOf_image_of_CValues_on_closedSet
      F K X hX f hC hLevel v hv
  have hBsubC : B ⊆ C := by
    intro w hw
    exact ((birthBlockOf_mem_iff F K v w).mp hw).1
  have hfC : ∀ u ∈ C, ∀ w ∈ C, f u = f w → u = w := by
    intro u hu w hw h
    exact hf u (hCX u hu) w (hCX w hw) h
  have hAdjC : ∀ u ∈ C, ∀ w ∈ C,
      G.adj u w ↔ G.adj (f u) (f w) := by
    intro u hu w hw
    exact hAdj u (hCX u hu) w (hCX w hw)
  have hDiff : (C \ B).image f = C' \ B' := by
    calc
      (C \ B).image f = C.image f \ B.image f :=
        finite_image_sdiff_on f C B hBsubC hfC
      _ = C' \ B' := by rw [hCv, hBv]
  have hNImage : N.image f = N' := by
    change (G.oldNeighbourSet (C \ B) B).image f =
      G.oldNeighbourSet (C' \ B') B'
    calc
      (G.oldNeighbourSet (C \ B) B).image f =
          G.oldNeighbourSet ((C \ B).image f) (B.image f) :=
        G.oldNeighbourSet_image_on G f C hAdjC
          (C \ B) B Finset.sdiff_subset hBsubC
      _ = G.oldNeighbourSet (C' \ B') B' := by
        rw [hDiff, hBv]
  have hNsubC : N ⊆ C :=
    (G.oldNeighbourSet_subset (C \ B) B).trans Finset.sdiff_subset
  have hSrc : d.dClosedHull N C = birthSupportOf F K v :=
    birthSupportOf_eq_hull_inside F K v
  have hDst : d.dClosedHull N' C' = birthSupportOf F K (f v) :=
    birthSupportOf_eq_hull_inside F K (f v)
  calc
    (birthSupportOf F K v).image f =
        (d.dClosedHull N C).image f :=
      congrArg (Finset.image f) hSrc.symm
    _ = d.dClosedHull (N.image f) (C.image f) :=
      G.dClosedHull_image_on G f C hfC hAdjC N hNsubC
    _ = d.dClosedHull N' C' := by rw [hNImage, hCv]
    _ = birthSupportOf F K (f v) := hDst

/-- The complete auxiliary b-value is recovered under local
R,H preservation, inducedness and reflected birth levels. -/
theorem birthBValue_image_of_CValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hC : ∀ v ∈ X,
      (birthCValue F K v).image f = birthCValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (v : Vertex F K) (hv : v ∈ X) :
    (birthBValue F K v).image f = birthBValue F K (f v) := by
  rw [birthBValue_eq_support_union_block F K v,
    birthBValue_eq_support_union_block F K (f v),
    Finset.image_union,
    birthSupportOf_image_of_CValues_on_closedSet
      F K X hX f hf hAdj hC hLevel v hv,
    birthBlockOf_image_of_CValues_on_closedSet
      F K X hX f hC hLevel v hv]

/-- Full RH-to-b transport on any possibly infinite b-closed
source X, with inducedness, injectivity, reflected level preorder,
and exact R/H-value preservation only on X. -/
theorem RHValues_imply_bValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hR : ∀ v ∈ X,
      (birthReachableRoots F K v).image f =
        birthReachableRoots F K (f v))
    (hH : ∀ s : Finset (Vertex F K),
      (∀ r ∈ s, r ∈ X) →
      (∀ r ∈ s, IsBirthRoot F K r) →
      (birthDClosedHull F K s).image f =
        birthDClosedHull F K (s.image f)) :
    ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) := by
  have hC : ∀ v ∈ X,
      (birthCValue F K v).image f = birthCValue F K (f v) :=
    birthCValue_image_of_RHValues_on_closedSet F K X hX f hR hH
  intro v hv
  exact birthBValue_image_of_CValues_on_closedSet F K X hX f
    hf hAdj hC hLevel v hv

/-- Complete equivalence of b- and (R,H)-value preservation on
arbitrary closed C_F source subsets, including reflection of
the partial H-domain on all source finite sets. The map is
subject to no conditions outside the source X.

It remains to expose an API with a literal map whose type is
the subtype X, rather than an arbitrary total extension f;
no assumption that such an extension is a global embedding
appears anywhere in this theorem. -/
theorem bValues_iff_RHValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f) :
    (∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        ((∀ r ∈ s, IsBirthRoot F K r) ↔
          (∀ r ∈ s.image f, IsBirthRoot F K r))) := by
  constructor
  · intro hB
    obtain ⟨hR, hHAll, hDomain⟩ :=
      bValues_imply_RHValues_on_closedSet F K X hX f
        hf hAdj hB hLevel hOrder
    exact ⟨hR, fun s hs _ => hHAll s hs, hDomain⟩
  · rintro ⟨hR, hH, _⟩
    exact RHValues_imply_bValues_on_closedSet F K X hX f
      hf hAdj hLevel hR hH

end CFCoherentTower
end BigHrushovski
