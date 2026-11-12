import BigHrushovski.CFPartialStageSupportOrder

/-!
# Pointwise agreement of the literal finite-stage support isomorphism

The finite-stage support order isomorphism built from an arbitrary
partial source embedding must send every old support coordinate to
the literal finite-stage coordinate of that vertex's image.
Merely knowing that there exists *some* order isomorphism between
the two supports is not enough to identify the actual ordered
local adjacency matrix of a target request.

This lemma extracts the exact pointwise equation already present
in the construction of the partial-stage support isomorphism.
The source embedding is evaluated only on the selected named
support. The result includes empty supports and target U_0.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The order isomorphism between literal finite-stage supports
has exactly the coordinates selected by the ORIGINAL partial
finite source map, pointwise on each old support vertex. -/
theorem finiteStageSupportOrderIso_apply_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ)
    (P : Finset (stage F K n).carrier)
    (Q : Finset (stage F K m).carrier)
    (hP : P.image (toVertex F K n) ⊆ s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (hImage :
      (selectedFiniteSet s
        (P.image (toVertex F K n))).image e =
          Q.image (toVertex F K m))
    (hOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (u : SupportCarrier (stage F K n).carrier P) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier :=
      stageLinearOrder F K m
    toVertex F K m
      (finiteStageSupportOrderIso
        F K s n m P Q hP e hImage hOrder u).val =
      e (finiteStageSupportPoint F K s n P hP u) := by
  classical
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  have hExist : ∀ z : SupportCarrier (stage F K n).carrier P,
      ∃ q : SupportCarrier (stage F K m).carrier Q,
        toVertex F K m q.val =
          e (finiteStageSupportPoint F K s n P hP z) := by
    intro z
    have hzSelected :=
      finiteStageSupportPoint_selected F K s n P hP z
    have hTarget :
        e (finiteStageSupportPoint F K s n P hP z) ∈
          Q.image (toVertex F K m) := by
      rw [← hImage]
      exact Finset.mem_image.mpr
        ⟨finiteStageSupportPoint F K s n P hP z,
          hzSelected, rfl⟩
    obtain ⟨q, hq, hqEq⟩ := Finset.mem_image.mp hTarget
    exact ⟨⟨q, hq⟩, hqEq⟩
  have hCoord := Classical.choose_spec (hExist u)
  unfold finiteStageSupportOrderIso
  dsimp
  exact hCoord

end CFCoherentTower
end BigHrushovski
