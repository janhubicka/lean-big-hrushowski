import BigHrushovski.C0FunctionalFiniteResponse
import BigHrushovski.InitialSegmentLabels

/-!
# Relabelling a finite C₀ functional response by consecutive coordinates

The finite tagged functional response has an arbitrary finite carrier.
The verified graph label construction already provides an equivalence
of that carrier with Fin(card carrier), keeping every old finite-stage
coordinate unchanged. The induced graph and the *entire* canonical
set-valued unary operation are transported through the same
equivalence, using the existing finite C₀ relabelling theorems.

This is the relabelling interface for a future countable fair functional
stage recursion. It proves no existence of a responding sequence and
does not silently replace a non-closed strong graph base by a closed
functional base.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every finite canonical functional presentation can be transported
to the consecutive Fin(card V) carrier while fixing all old
coordinates prescribed by a finite induced source map. Both graph
edges and nonedges and all complete unary values are preserved.

If the original old factor is a canonical structure with index κA
and the new canonical function extends its complete values along i,
the relabelled response also preserves those named values exactly
along the new old embedding. -/
theorem exists_initialSegment_canonicalFunctionalExtension
    {A B : Type*}
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n m : ℕ}
    (G : GraphOn A) (K : GraphOn B)
    (κA : A → Fin n) (κK : B → Fin m)
    (hStages : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κK k = FiniteC0.oldStage κK (k+1) ∨
      K.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κK k)
        (FiniteC0.oldStage κK (k+1)))
    (i : A → B) (hi : Function.Injective i)
    (old : A ≃ Fin (Fintype.card A))
    (hOldValues : ∀ a : A,
      FiniteC0.canonicalValue K κK (i a) =
        (FiniteC0.canonicalValue G κA a).image i) :
    ∃ (M : FiniteFunctionalC0 (Fintype.card B) m)
      (label : B ≃ Fin (Fintype.card B)),
      (∀ a : A, (label (i a)).val = (old a).val) ∧
      (∀ x y : B,
        K.adj x y ↔ M.graph.adj (label x) (label y)) ∧
      (∀ x : B,
        M.unaryValue (label x) =
          (FiniteC0.canonicalValue K κK x).image label) ∧
      (∀ a : A,
        M.unaryValue (label (i a)) =
          (FiniteC0.canonicalValue G κA a).image
            (fun u => label (i u))) := by
  classical
  let label : B ≃ Fin (Fintype.card B) :=
    FiniteSpan.extendInitialEquiv i hi old
  let H : GraphOn (Fin (Fintype.card B)) :=
    K.pullback label.symm
  have hAdj : ∀ x y : B,
      K.adj x y ↔ H.adj (label x) (label y) := by
    intro x y
    change K.adj x y ↔
      K.adj (label.symm (label x)) (label.symm (label y))
    simp
  let κNew : Fin (Fintype.card B) → Fin m :=
    FiniteC0.relabelIndex κK label
  have hNewStages : ∀ j : ℕ, j < m →
      FiniteC0.oldStage κNew j =
        FiniteC0.oldStage κNew (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κNew j)
        (FiniteC0.oldStage κNew (j+1)) :=
    FiniteC0.minimalSteps_relabel K H label hAdj κK hStages
  let M : FiniteFunctionalC0 (Fintype.card B) m :=
    ⟨H, κNew, hNewStages⟩
  refine ⟨M, label, ?_, hAdj, ?_, ?_⟩
  · intro a
    exact FiniteSpan.extendInitialEquiv_old i hi old a
  · intro x
    exact FiniteC0.canonicalValue_relabel
      K H label hAdj κK x
  · intro a
    calc
      M.unaryValue (label (i a)) =
        (FiniteC0.canonicalValue K κK (i a)).image label :=
          FiniteC0.canonicalValue_relabel
            K H label hAdj κK (i a)
      _ = ((FiniteC0.canonicalValue G κA a).image i).image
          label := by rw [hOldValues a]
      _ = (FiniteC0.canonicalValue G κA a).image
          (fun u => label (i u)) := by
            rw [Finset.image_image]
            rfl

end FiniteCatalogue
end BigHrushovski
