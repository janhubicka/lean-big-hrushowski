import BigHrushovski.CFSelectedBatchImage
import BigHrushovski.CFExactOldFreshBoundary

/-!
# One simultaneous map of all selected tagged C_F blocks

The finite level-lifting argument requires *all* chosen blocks at a
represented source level to be sent to blocks at the same prescribed
target level. A series of one-block responses does not suffice.

Represent the source as its selected old finite carrier together with
a dependent sum of the selected tagged fresh blocks. A map of request
tags and a map of each finite ordinal interval determine one map of
the entire selected carrier. This is a single finite graph map, not a
chronological sequence of one-block extensions.

We prove its injectivity and the full induced-graph criterion. Different
source request tags are disjoint and no two distinct target tags can
supply a cross-block edge. For old-fresh pairs and pairs within a
block, the exact induced boundary and local graph equalities remain
explicit premises, to be discharged by the constructed request
transport of the preceding modules.

The d-closed image and preservation of the precise global order are
separate lemmas, so no unverified finite lift is asserted here.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- The selected *literal* request records, retaining membership in
the original finite family. -/
abbrev SelectedRequests
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (D : Finset (Requests G Allowed bound)) :=
  {r : Requests G Allowed bound // r ∈ D}

/-- All fresh ordinals of the chosen request tags; no fresh
vertices from unselected requests are included. -/
abbrev SelectedFresh
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (D : Finset (Requests G Allowed bound)) :=
  Σ r : SelectedRequests G Allowed bound D, Fin r.1.code.1.val

/-- The selected old source together with the complete chosen
fresh blocks, represented as one finite disjoint sum. -/
abbrev SelectedCarrier
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound)) :=
  Sum (SupportCarrier U S) (SelectedFresh G Allowed bound D)

/-- The source carrier has its literal inclusion into the actual
simultaneous tagged level of the original finite graph. -/
def selectedSourceMap
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound)) :
    SelectedCarrier G Allowed bound S D →
      LevelCarrier G Allowed bound
  | Sum.inl u => Sum.inl u.val
  | Sum.inr ⟨r, i⟩ => Sum.inr ⟨r.val, i⟩

/-- The entire selected batch is mapped at once: old vertices
follow f, and a fresh vertex (r,i) follows its specified target
request tag and fresh ordinal image. -/
def selectedTargetMap
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (f : U → V)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.1.code.1.val → Fin (T r).code.1.val) :
    SelectedCarrier G Allowed bound S D →
      LevelCarrier H AllowedV boundV
  | Sum.inl u => Sum.inl (f u.val)
  | Sum.inr ⟨r, i⟩ => Sum.inr ⟨T r, phi r i⟩

/-- The selected source inclusion is injective on both old
vertices and dependent request-tagged fresh vertices. -/
theorem selectedSourceMap_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound)) :
    Function.Injective (selectedSourceMap G Allowed bound S D) := by
  intro x y h
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr v =>
          cases h
  | inr x =>
      cases y with
      | inl v =>
          cases h
      | inr y =>
          rcases x with ⟨r, i⟩
          rcases y with ⟨s, j⟩
          have hSigma :
              (⟨r.val, i⟩ : FreshCarrier G Allowed bound) =
                ⟨s.val, j⟩ := Sum.inr.inj h
          have hrs : r = s := Subtype.ext
            (congrArg Sigma.fst hSigma)
          cases hrs
          have hij : i = j := by
            apply Fin.ext
            exact congrArg (fun z : FreshCarrier G Allowed bound =>
              z.2.val) hSigma
          cases hij
          rfl

/-- The full simultaneous map is injective when the old map is
injective on the selected source, the request map is injective,
and each ordinal map is injective. -/
theorem selectedTargetMap_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (f : U → V)
    (hf : Set.InjOn f S)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hT : Function.Injective T)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.1.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ r, Function.Injective (phi r)) :
    Function.Injective
      (selectedTargetMap G Allowed bound H AllowedV boundV
        S D f T phi) := by
  intro x y h
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply hf u.property v.property
          exact Sum.inl.inj h
      | inr v =>
          cases h
  | inr x =>
      cases y with
      | inl v =>
          cases h
      | inr y =>
          rcases x with ⟨r, i⟩
          rcases y with ⟨s, j⟩
          have hSigma :
              (⟨T r, phi r i⟩ : FreshCarrier H AllowedV boundV) =
                ⟨T s, phi s j⟩ := Sum.inr.inj h
          have hrs : r = s := hT (congrArg Sigma.fst hSigma)
          cases hrs
          have hij : i = j := by
            apply hphi r
            apply Fin.ext
            exact congrArg
              (fun z : FreshCarrier H AllowedV boundV => z.2.val)
              hSigma
          cases hij
          rfl

/-- Exact inducedness of the simultaneous map reduces to three
local types of comparison: old-old, old-fresh, and fresh-fresh
within *one* request. Different requests have no connecting
edge on either side, by the actual tagged graph construction. -/
theorem selectedTargetMap_induced
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (f : U → V)
    (hOld : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (f u.val) (f v.val))
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hT : Function.Injective T)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.1.code.1.val → Fin (T r).code.1.val)
    (hBoundary : ∀ (u : SupportCarrier U S)
        (r : SelectedRequests G Allowed bound D)
        (i : Fin r.1.code.1.val),
      (levelGraph G Allowed bound).adj
        (Sum.inl u.val) (Sum.inr ⟨r.val, i⟩) ↔
      (levelGraph H AllowedV boundV).adj
        (Sum.inl (f u.val)) (Sum.inr ⟨T r, phi r i⟩))
    (hFresh : ∀ (r : SelectedRequests G Allowed bound D)
        (i j : Fin r.1.code.1.val),
      (levelGraph G Allowed bound).adj
        (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨r.val, j⟩) ↔
      (levelGraph H AllowedV boundV).adj
        (Sum.inr ⟨T r, phi r i⟩)
        (Sum.inr ⟨T r, phi r j⟩))
    (x y : SelectedCarrier G Allowed bound S D) :
    (levelGraph G Allowed bound).adj
      (selectedSourceMap G Allowed bound S D x)
      (selectedSourceMap G Allowed bound S D y) ↔
    (levelGraph H AllowedV boundV).adj
      (selectedTargetMap G Allowed bound H AllowedV boundV
        S D f T phi x)
      (selectedTargetMap G Allowed bound H AllowedV boundV
        S D f T phi y) := by
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          exact (levelGraph_old_iff G Allowed bound u.val v.val).trans
            ((hOld u v).trans
              (levelGraph_old_iff H AllowedV boundV (f u.val) (f v.val)).symm)
      | inr x =>
          rcases x with ⟨r, i⟩
          exact hBoundary u r i
  | inr x =>
      rcases x with ⟨r, i⟩
      cases y with
      | inl v =>
          constructor
          · intro h
            have hOldFresh : (levelGraph G Allowed bound).adj
                (Sum.inl v.val) (Sum.inr ⟨r.val, i⟩) :=
              (levelGraph G Allowed bound).symm _ _ h
            exact (levelGraph H AllowedV boundV).symm _ _
              ((hBoundary v r i).mp hOldFresh)
          · intro h
            have hOldFresh : (levelGraph H AllowedV boundV).adj
                (Sum.inl (f v.val)) (Sum.inr ⟨T r, phi r i⟩) :=
              (levelGraph H AllowedV boundV).symm _ _ h
            exact (levelGraph G Allowed bound).symm _ _
              ((hBoundary v r i).mpr hOldFresh)
      | inr y =>
          rcases y with ⟨s, j⟩
          by_cases hrs : r = s
          · subst s
            exact hFresh r i j
          · have hSrc :
                ¬ (levelGraph G Allowed bound).adj
                  (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨s.val, j⟩) :=
              levelGraph_no_cross_fresh G Allowed bound
                r.val s.val (fun eq => hrs (Subtype.ext eq)) i j
            have hTNe : T r ≠ T s := fun eq => hrs (hT eq)
            have hDst :
                ¬ (levelGraph H AllowedV boundV).adj
                  (Sum.inr ⟨T r, phi r i⟩)
                  (Sum.inr ⟨T s, phi s j⟩) :=
              levelGraph_no_cross_fresh H AllowedV boundV
                (T r) (T s) hTNe (phi r i) (phi s j)
            exact iff_of_false hSrc hDst

end CFStageCatalogue
end BigHrushovski
