import BigHrushovski.C0FunctionalNatStageTransport
import BigHrushovski.C0FiniteEquivTransport

/-!
# Literal finite C₀ canonical certificates on Nat initial segments

A finite canonical functional graph is a graph on Fin n with
its minimal-component index. Its Nat-supported graph and
complete unary operation, obtained by the literal value map
Fin n → ℕ, must satisfy the *same* finite canonical
presentation on the actual subtype of range n.

We use the explicit bijection Fin n ≃ {x : ℕ // x < n}.
It fixes numerical vertices pointwise. All minimal strong
steps and complete unary values transport through that
induced bijection, including reflection of nonedges.
No arbitrary chosen finite numbering is involved.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- The exact enumeration of a consecutive finite Nat interval
by its original finite ordinal: no old label is permuted. -/
def finRangeEquiv (n : ℕ) :
    Fin n ≃ {x : ℕ // x ∈ Finset.range n} where
  toFun x := ⟨x.val, Finset.mem_range.mpr x.isLt⟩
  invFun x := ⟨x.val, Finset.mem_range.mp x.property⟩
  left_inv := by
    intro x
    apply Fin.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

@[simp] theorem finRangeEquiv_apply_val (n : ℕ) (x : Fin n) :
    ((finRangeEquiv n) x).val = x.val := rfl

@[simp] theorem finRangeEquiv_symm_val (n : ℕ)
    (x : {x : ℕ // x ∈ Finset.range n}) :
    ((finRangeEquiv n).symm x).val = x.val := rfl

/-- The literal Nat-range induced graph is an exact relabelling
of the original finite graph, including absence of edges. -/
theorem natGraph_range_induced (s : FiniteFunctionalNatStage)
    (x y : Fin s.size) :
    s.model.graph.adj x y ↔
      (s.natGraph.pullback
        (Subtype.val : {x : ℕ // x ∈ Finset.range s.size} → ℕ)).adj
        (finRangeEquiv s.size x) (finRangeEquiv s.size y) := by
  exact s.natGraph_induced x y

/-- The entire canonical finite C₀ presentation transports to
the literal Nat interval, with all minimal steps and *complete*
one-generated unary values, without changing numeric labels. -/
theorem exists_canonical_natStage (s : FiniteFunctionalNatStage) :
    ∃ (k : ℕ)
      (κ : {x : ℕ // x ∈ Finset.range s.size} → Fin k),
      (∀ j : ℕ, j < k →
        FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
        (s.natGraph.pullback
          (Subtype.val :
            {x : ℕ // x ∈ Finset.range s.size} → ℕ)).toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κ j)
          (FiniteC0.oldStage κ (j+1))) ∧
      (∀ x : {x : ℕ // x ∈ Finset.range s.size},
        s.natValue x.val =
          (FiniteC0.canonicalValue
            (s.natGraph.pullback
              (Subtype.val :
                {x : ℕ // x ∈ Finset.range s.size} → ℕ))
            κ x).image
              (Subtype.val :
                {x : ℕ // x ∈ Finset.range s.size} → ℕ)) := by
  classical
  let e := finRangeEquiv s.size
  let H : GraphOn {x : ℕ // x ∈ Finset.range s.size} :=
    s.natGraph.pullback
      (Subtype.val : {x : ℕ // x ∈ Finset.range s.size} → ℕ)
  let κ := FiniteC0.relabelIndex s.model.index e
  have hAdj : ∀ x y : Fin s.size,
      s.model.graph.adj x y ↔ H.adj (e x) (e y) :=
    s.natGraph_range_induced
  have hSteps : ∀ j : ℕ, j < s.blocks →
      FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ j) (FiniteC0.oldStage κ (j+1)) :=
    FiniteC0.minimalSteps_relabel
      s.model.graph H e hAdj s.model.index s.model.minimal
  refine ⟨s.blocks, κ, hSteps, ?_⟩
  intro x
  let u : Fin s.size := e.symm x
  have hxSize : x.val < s.size :=
    Finset.mem_range.mp x.property
  have hOldPoint : (⟨x.val, hxSize⟩ : Fin s.size) = u := by
    apply Fin.ext
    exact (finRangeEquiv_symm_val s.size x).symm
  have hTransport :
      FiniteC0.canonicalValue H κ (e u) =
        (s.model.unaryValue u).image e :=
    FiniteC0.canonicalValue_relabel
      s.model.graph H e hAdj s.model.index u
  calc
    s.natValue x.val =
        (s.model.unaryValue u).image
          (fun z : Fin s.size => z.val) := by
        rw [s.natValue_inside x.val hxSize, hOldPoint]
    _ = ((s.model.unaryValue u).image e).image
        (Subtype.val :
          {x : ℕ // x ∈ Finset.range s.size} → ℕ) := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro z hz
        rfl
    _ = (FiniteC0.canonicalValue H κ x).image
        (Subtype.val :
          {x : ℕ // x ∈ Finset.range s.size} → ℕ) := by
        rw [← e.apply_symm_apply x, hTransport]

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
