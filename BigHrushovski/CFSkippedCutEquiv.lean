import BigHrushovski.CFRepresentedLevels

/-!
# Canonical identification across an unrepresented C_F birth level

When a finite b-closed source contains no vertex born at level n,
its cut in the next stage contains exactly the old vertices,
embedded literally by Sum.inl. There is a unique canonical
equivalence between the two finite cut subtypes.

This is the persistence step for the finite-level lifting
induction. It does not introduce new target blocks, change
their codes, or require an increasing map on all ambient levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The old-stage inclusion is a bijection between actual
source cuts across an unrepresented birth level. -/
noncomputable def skippedCutEquiv
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ)
    (hn : n ∉ representedLevels F K s) :
    SupportCarrier (stage F K n).carrier (stageCut F K s n) ≃
      SupportCarrier (stage F K (n+1)).carrier
        (stageCut F K s (n+1)) := by
  classical
  let f : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) →
      SupportCarrier (stage F K (n+1)).carrier
        (stageCut F K s (n+1)) :=
    fun u => ⟨Sum.inl u.val, by
      rw [stageCut_succ_eq_old_of_unrepresented F K s hs n hn]
      exact Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hab))
  · intro v
    have hv : v.val ∈ (stageCut F K s n).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n+1)).carrier) := by
      rw [← stageCut_succ_eq_old_of_unrepresented F K s hs n hn]
      exact v.property
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

/-- The skipped-level identification acts literally by
the old-stage embedding Sum.inl. -/
theorem skippedCutEquiv_val
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ)
    (hn : n ∉ representedLevels F K s)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (skippedCutEquiv F K s hs n hn u).val = Sum.inl u.val := by
  rfl

/-- An unrepresented source step preserves and reflects
the complete induced graph, including absent edges. -/
theorem skippedCutEquiv_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ)
    (hn : n ∉ representedLevels F K s)
    (u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    (stage F K n).graph.adj u.val v.val ↔
      (stage F K (n+1)).graph.adj
        (skippedCutEquiv F K s hs n hn u).val
        (skippedCutEquiv F K s hs n hn v).val := by
  rw [skippedCutEquiv_val, skippedCutEquiv_val]
  exact (stage_succ_induced F K n u.val v.val).symm

end CFCoherentTower
end BigHrushovski
