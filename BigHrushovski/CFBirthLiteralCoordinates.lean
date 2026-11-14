import BigHrushovski.CFBirthLocalRoots
import BigHrushovski.CFBlockOrdinalRigidity

/-!
# Literal coordinates and cardinalities of C_F birth blocks

The old support of a birth request is exactly the image of its
named support in the preceding finite stage. Its new block is
exactly the image of the full finite ordinal interval of its
request code. These are equalities of actual birth-labelled
vertex sets, not abstract isomorphisms.

They provide the finite cardinality and old-support preimage
interfaces needed to recover the local ordered request code
of an arbitrary finite functional embedding. In particular,
the block size is the fresh-size field of its request record.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The old named support of a request, in the countable birth
carrier, is exactly the image of its literal finite-stage
support under the canonical map. -/
theorem birthSupport_eq_stageSupport_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    birthSupport F K n r =
      r.support.image (toVertex F K n) := by
  classical
  change
    (r.support.image (Sum.inl :
        (stage F K n).carrier →
          (stage F K (n+1)).carrier)).image
      (toVertex F K (n+1)) =
        r.support.image (toVertex F K n)
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    rw [← huw] at hwv
    exact Finset.mem_image.mpr
      ⟨u, hu, by simpa only [toVertex_old] using hwv⟩
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨Sum.inl u,
        Finset.mem_image.mpr ⟨u, hu, rfl⟩,
        by simpa only [toVertex_old] using huv⟩

/-- A vertex belongs to an actual birth support if and only
if it is the canonical image of a vertex of the named old
finite-stage support. -/
theorem mem_birthSupport_iff_old
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (v : Vertex F K) :
    v ∈ birthSupport F K n r ↔
      ∃ u : (stage F K n).carrier,
        u ∈ r.support ∧ toVertex F K n u = v := by
  rw [birthSupport_eq_stageSupport_image]
  exact Finset.mem_image

/-- The entire new birth block is literally the image of
the full finite ordered ordinal interval. -/
theorem birthBlock_eq_fresh_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    birthBlock F K n r =
      (Finset.univ : Finset (Fin r.code.1.val)).image
        (fun i => (⟨n, ⟨r, i⟩⟩ : Vertex F K)) := by
  classical
  change
    ((Finset.univ : Finset (Fin r.code.1.val)).image
      (fun i => (Sum.inr (⟨r, i⟩ : FreshAt F K n) :
        (stage F K (n+1)).carrier))).image
          (toVertex F K (n+1)) =
      (Finset.univ : Finset (Fin r.code.1.val)).image
        (fun i => (⟨n, ⟨r, i⟩⟩ : Vertex F K))
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨i, _, hiw⟩ := Finset.mem_image.mp hw
    rw [← hiw] at hwv
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _,
        by simpa only [toVertex_new] using hwv⟩
  · intro hv
    obtain ⟨i, _, hiv⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨Sum.inr ⟨r, i⟩,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        by simpa only [toVertex_new] using hiv⟩

/-- Every actual birth block has exactly the fresh cardinality
stored in its request code. Multiple ordinal values may not
collapse, since the birth vertex retains its ordinal index. -/
theorem birthBlock_card
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    (birthBlock F K n r).card = r.code.1.val := by
  classical
  rw [birthBlock_eq_fresh_image]
  have hInj : Function.Injective
      (fun i : Fin r.code.1.val =>
        (⟨n, ⟨r, i⟩⟩ : Vertex F K)) := by
    intro i j hij
    apply Fin.ext
    exact congrArg
      (fun v : Vertex F K => v.2.2.val) hij
  calc
    ((Finset.univ : Finset (Fin r.code.1.val)).image
        (fun i => (⟨n, ⟨r, i⟩⟩ : Vertex F K))).card =
      (Finset.univ : Finset (Fin r.code.1.val)).card :=
        Finset.card_image_of_injective _ hInj
    _ = r.code.1.val := by simp

/-- No support vertex is accidentally duplicated by its
canonical inclusion into the countable birth carrier. -/
theorem birthSupport_card
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    (birthSupport F K n r).card = r.support.card := by
  rw [birthSupport_eq_stageSupport_image]
  exact Finset.card_image_of_injective _
    (toVertex_injective F K n)

end CFCoherentTower
end BigHrushovski
