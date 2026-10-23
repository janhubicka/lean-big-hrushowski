import BigHrushovski.C0TaggedMinimalStages
import BigHrushovski.C0MinimalImage

/-!
# All old minimal strong stages survive a tagged free C0 join

The left-order-fixed joined index has exactly the original old
left-stage vertex sets up to its boundary rank n. Each induced
left-stage graph is isomorphic to its source, so the existing
minimal strong step image theorem transports EVERY old step.
Empty old steps are retained unchanged.

This is part of the final canonical finite functional free
amalgamation proof. Appended right-tail steps are treated separately.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

theorem joinedIndex_old_minimal_steps
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hSteps : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κL k =
        FiniteC0.oldStage κL (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κL k)
        (FiniteC0.oldStage κL (k+1))) :
    ∀ k : ℕ, k < n →
      FiniteC0.oldStage (joinedIndex κL κR) k =
        FiniteC0.oldStage (joinedIndex κL κR) (k+1) ∨
      (freeGraph G H).toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage (joinedIndex κL κR) k)
        (FiniteC0.oldStage (joinedIndex κL κR) (k+1)) := by
  intro k hk
  have hK := joinedIndex_oldStage_before κL κR k (by omega)
  have hSucc := joinedIndex_oldStage_before κL κR (k+1) (by omega)
  rcases hSteps k hk with hEq | hMin
  · left
    rw [hK, hSucc, hEq]
  · right
    rw [hK, hSucc]
    have hSubset :
        FiniteC0.oldStage κL k ⊆
        FiniteC0.oldStage κL (k+1) := by
      intro u hu
      have hv := (FiniteC0.mem_oldStage_iff κL k u).mp hu
      exact (FiniteC0.mem_oldStage_iff κL (k+1) u).mpr
        (by omega)
    exact (G.minimalStrongStep_image_iff (freeGraph G H)
      (leftTag : Sum P L → Carrier P L R)
      leftTag_injective
      (fun x y => (freeGraph_left G H hAgree x y).symm)
      (FiniteC0.oldStage κL k)
      (FiniteC0.oldStage κL (k+1)) hSubset).mpr hMin

end TaggedAmalgam
end BigHrushovski
