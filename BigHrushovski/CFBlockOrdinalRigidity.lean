import BigHrushovski.CFCanonicalOrderEmbedding
import Mathlib.Order.Fin.Basic

/-!
# Every position in a complete ordered C_F block is preserved

The complete image of a birth block, together with its increasing
order, determines every fresh ordinal, not just the first vertex.
This removes the ordinal-equality premise from the uniqueness
argument for finite level lifting.

All embedding hypotheses are restricted to the closed source. The
source may be empty or infinite. No graph response, existence of a
level lift, or nonemptiness of all levels is asserted here.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Membership in a literal block retains exactly its request tag
and one of its fresh ordinal indices. -/
theorem mem_birthBlock_iff_exists_ordinal
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) (v : Vertex F K) :
    v ∈ birthBlock F K n r ↔
      ∃ i : Fin r.code.1.val,
        v = (⟨n, ⟨r, i⟩⟩ : Vertex F K) := by
  classical
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
    obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hz
    refine ⟨i, ?_⟩
    calc
      v = toVertex F K (n + 1) z := hzv.symm
      _ = toVertex F K (n + 1) (Sum.inr ⟨r, i⟩) := by rw [hiz]
      _ = (⟨n, ⟨r, i⟩⟩ : Vertex F K) := rfl
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr
      ⟨Sum.inr ⟨r, i⟩,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩

/-- An increasing surjection between finite ordinal intervals
preserves each ordinal exactly. Mere injectivity would not suffice. -/
theorem fin_value_eq_of_strictMono_surjective
    {m n : ℕ} (f : Fin m → Fin n)
    (hMono : StrictMono f) (hOnto : Function.Surjective f)
    (i : Fin m) : (f i).val = i.val := by
  let e : Fin m ≃o Fin n :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hMono) hOnto
  exact Fin.coe_orderIso_apply e i

/-- An increasing map onto a complete target birth block fixes
every ordinal in that block. The source and target levels and
requests can differ. -/
theorem birthOrdinal_eq_of_complete_block_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ) (r : BirthRequest F K n) (s : BirthRequest F K m)
    (f : Vertex F K → Vertex F K)
    (hImage : (birthBlock F K n r).image f = birthBlock F K m s)
    (hOrder : ∀ i j : Fin r.code.1.val, i.val < j.val →
      birthOrdinal F K (f ⟨n, ⟨r, i⟩⟩) <
        birthOrdinal F K (f ⟨n, ⟨r, j⟩⟩))
    (i : Fin r.code.1.val) :
    birthOrdinal F K (f ⟨n, ⟨r, i⟩⟩) = i.val := by
  classical
  have hTarget : ∀ j : Fin r.code.1.val,
      ∃ k : Fin s.code.1.val,
        f (⟨n, ⟨r, j⟩⟩ : Vertex F K) = ⟨m, ⟨s, k⟩⟩ := by
    intro j
    apply (mem_birthBlock_iff_exists_ordinal F K m s _).mp
    rw [← hImage]
    exact Finset.mem_image.mpr
      ⟨⟨n, ⟨r, j⟩⟩,
        (mem_birthBlock_iff_exists_ordinal F K n r _).mpr ⟨j, rfl⟩,
        rfl⟩
  let g : Fin r.code.1.val → Fin s.code.1.val :=
    fun j => Classical.choose (hTarget j)
  have hg : ∀ j : Fin r.code.1.val,
      f (⟨n, ⟨r, j⟩⟩ : Vertex F K) = ⟨m, ⟨s, g j⟩⟩ :=
    fun j => Classical.choose_spec (hTarget j)
  have hMono : StrictMono g := by
    intro j k hjk
    have h := hOrder j k hjk
    rw [hg j, hg k] at h
    exact h
  have hOnto : Function.Surjective g := by
    intro j
    have hj : (⟨m, ⟨s, j⟩⟩ : Vertex F K) ∈
        (birthBlock F K n r).image f := by
      rw [hImage]
      exact (mem_birthBlock_iff_exists_ordinal F K m s _).mpr ⟨j, rfl⟩
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
    obtain ⟨k, rfl⟩ := (mem_birthBlock_iff_exists_ordinal F K n r v).mp hv
    refine ⟨k, Fin.ext ?_⟩
    have h := congrArg (birthOrdinal F K) ((hg k).symm.trans hfv)
    exact h
  rw [hg i]
  exact fin_value_eq_of_strictMono_surjective g hMono hOnto i

/-- Complete b-values and the level preorder recover whole block
images. Increasing order on those blocks then preserves every
internal ordinal, with hypotheses only on the closed source. -/
theorem birthOrdinal_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f)
    (v : Vertex F K) (hv : v ∈ X) :
    birthOrdinal F K (f v) = birthOrdinal F K v := by
  classical
  rcases v with ⟨n, ⟨r, i⟩⟩
  have hImage := birthBlockOf_image_on_closedSet F K X hX f hB hLevel
    (⟨n, ⟨r, i⟩⟩ : Vertex F K) hv
  let w := f (⟨n, ⟨r, i⟩⟩ : Vertex F K)
  have hLiteral : (birthBlock F K n r).image f =
      birthBlock F K w.1 w.2.1 := hImage
  apply birthOrdinal_eq_of_complete_block_image F K n w.1 r w.2.1 f hLiteral
  intro j k hjk
  exact hOrder (⟨n, ⟨r, i⟩⟩ : Vertex F K) hv
    (⟨n, ⟨r, j⟩⟩ : Vertex F K) (⟨n, ⟨r, k⟩⟩ : Vertex F K)
    ((mem_birthBlock_iff_exists_ordinal F K n r _).mpr ⟨j, rfl⟩)
    ((mem_birthBlock_iff_exists_ordinal F K n r _).mpr ⟨k, rfl⟩) hjk

/-- For the manuscript's exact canonical order, every embedding
preserving complete b-values fixes the internal block ordinals.
Ordinal preservation is a conclusion, not an extra hypothesis. -/
theorem birthOrdinal_image_on_closedSet_of_canonicalOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : ∀ u ∈ X, ∀ v ∈ X,
      canonicalBirthLt F K u v ↔ canonicalBirthLt F K (f u) (f v))
    (v : Vertex F K) (hv : v ∈ X) :
    birthOrdinal F K (f v) = birthOrdinal F K v := by
  exact birthOrdinal_image_on_closedSet F K X hX f hB hLevel
    (preservesBirthBlockOrderOn_of_compatibleOrder F K X hX f hB hLevel
      (canonicalBirthLt F K) (canonicalBirthLt_compatible F K) hOrder) v hv

end CFCoherentTower
end BigHrushovski
