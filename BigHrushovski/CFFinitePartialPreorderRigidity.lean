import BigHrushovski.CFFinitePartialLevelPartition
import BigHrushovski.CFBirthFirstOrder

/-!
# Exact finite C_F block images from the birth-level preorder

The finite ᶜ_F embedding language already records the birth-level
preorder. An embedding of a finite selected source that reflects this
preorder, maps a given fresh vertex to a prescribed target vertex,
and preserves its COMPLETE auxiliary b-value must send the whole
source support and fresh block onto the corresponding target sets.

In particular, the old/new label hypotheses from the elementary
partition lemma are consequences of the existing preorder
reflection. This proof does not need a total map on the
countable universe or any chosen global map of birth indices.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- A partial finite map reflecting the actual birth-level preorder
recovers both parts of a complete birth b-value exactly. There is
NO whole-block surjectivity or support-image premise, and the map
is defined only on the selected subtype of s. -/
theorem finitePartial_birthSupport_block_of_preorder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ)
    (r : BirthRequest F K n)
    (t : BirthRequest F K m)
    (i : Fin r.code.1.val)
    (j : Fin t.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (e : {v : Vertex F K // v ∈ s} → Vertex F K)
    (hValue :
      (selectedFiniteSet s (birthBValue F K
        (⟨n, ⟨r, i⟩⟩ : Vertex F K))).image e =
      birthBValue F K (⟨m, ⟨t, j⟩⟩ : Vertex F K))
    (hTarget :
      e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ =
        (⟨m, ⟨t, j⟩⟩ : Vertex F K))
    (hLevel : ∀ u v : {v : Vertex F K // v ∈ s},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v)) :
    (selectedFiniteSet s (birthSupport F K n r)).image e =
        birthSupport F K m t ∧
    (selectedFiniteSet s (birthBlock F K n r)).image e =
        birthBlock F K m t := by
  classical
  apply finitePartial_birthSupport_block_of_levelSplit
    F K s n m r t i j e hValue
  · intro u hu
    have huSupport : u.val ∈ birthSupport F K n r := by
      simpa [selectedFiniteSet] using hu
    have huOld : u.val.1 < n :=
      birthSupport_birth_lt F K n r huSupport
    apply lt_of_not_ge
    intro hge
    have hBack : n ≤ u.val.1 := by
      have h := (hLevel
        ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ u).mpr (by
          change (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).1 ≤ (e u).1
          rw [hTarget]
          exact hge)
      exact h
    exact (not_le_of_gt huOld) hBack
  · intro u hu
    have huBlock : u.val ∈ birthBlock F K n r := by
      simpa [selectedFiniteSet] using hu
    have hSame : u.val.1 = n :=
      birthBlock_birth_eq F K n r huBlock
    apply Nat.le_antisymm
    · have h := (hLevel u
          ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).mp (by
            change u.val.1 ≤ n
            exact hSame.le)
      change (e u).1 ≤
        (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).1 at h
      rw [hTarget] at h
      exact h
    · have h := (hLevel
          ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ u).mp (by
            change n ≤ u.val.1
            exact hSame.ge)
      change (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).1 ≤
        (e u).1 at h
      rw [hTarget] at h
      exact h

end CFCoherentTower
end BigHrushovski
