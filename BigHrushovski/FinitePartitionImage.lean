import Mathlib.Data.Finset.Image

/-!
# Recovering the two parts of a finite union from a separating label

If the image of a union is exactly a target union, and a predicate
separates the two source and target parts, then the images of
the two parts are exact separately. Injectivity is unnecessary.
This is common finite-set bookkeeping for the C₀ component and
C_F fresh-block presentations.
-/

namespace BigHrushovski

/-- Full-union image equality together with a predicate separating
old and new elements determines both images exactly. In particular,
one does not need to assume that the new block is mapped onto
the target new block once the label of each image is known. -/
theorem union_images_of_separated_parts
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (P B : Finset U) (Q C : Finset V)
    (e : U → V) (isNew : V → Prop)
    (hFull : (P ∪ B).image e = Q ∪ C)
    (hP : ∀ u ∈ P, ¬ isNew (e u))
    (hB : ∀ u ∈ B, isNew (e u))
    (hQ : ∀ v ∈ Q, ¬ isNew v)
    (hC : ∀ v ∈ C, isNew v) :
    P.image e = Q ∧ B.image e = C := by
  classical
  have hPto : P.image e ⊆ Q := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hUnion : e u ∈ Q ∪ C := by
      rw [← hFull]
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_union.mpr (Or.inl hu), rfl⟩
    rcases Finset.mem_union.mp hUnion with hq | hc
    · exact hq
    · exact (hP u hu (hC (e u) hc)).elim
  have hQto : Q ⊆ P.image e := by
    intro v hv
    have hUnion : v ∈ (P ∪ B).image e := by
      rw [hFull]
      exact Finset.mem_union.mpr (Or.inl hv)
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hUnion
    rcases Finset.mem_union.mp hu with hp | hb
    · exact Finset.mem_image.mpr ⟨u, hp, huv⟩
    · have hn : isNew v := by
        rw [← huv]
        exact hB u hb
      exact (hQ v hv hn).elim
  have hBto : B.image e ⊆ C := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hUnion : e u ∈ Q ∪ C := by
      rw [← hFull]
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_union.mpr (Or.inr hu), rfl⟩
    rcases Finset.mem_union.mp hUnion with hq | hc
    · exact (hQ (e u) hq (hB u hu)).elim
    · exact hc
  have hCto : C ⊆ B.image e := by
    intro v hv
    have hUnion : v ∈ (P ∪ B).image e := by
      rw [hFull]
      exact Finset.mem_union.mpr (Or.inr hv)
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hUnion
    rcases Finset.mem_union.mp hu with hp | hb
    · have ho : ¬ isNew v := by
        rw [← huv]
        exact hP u hp
      exact (ho (hC v hv)).elim
    · exact Finset.mem_image.mpr ⟨u, hb, huv⟩
  exact ⟨Finset.Subset.antisymm hPto hQto,
    Finset.Subset.antisymm hBto hCto⟩

end BigHrushovski
