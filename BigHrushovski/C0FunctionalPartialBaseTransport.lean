import BigHrushovski.C0FunctionalJointStepRecursion
import BigHrushovski.C0NamedClosedBaseValues

/-!
# Track A: the inverse of a closed functional partial isomorphism
  as a canonical finite-stage base embedding

Suppose a finite closed complete-functional partial isomorphism p
maps its source S to its target R. If the source S lies in a finite
canonical stage T, the inverse of p followed by the literal inclusion
S → T is an injective induced embedding of the whole target base R
into T.

The complete unary value at a vertex of this embedded base is
precisely the image of its *entire* named unary value in R. This
is the base-compatibility hypothesis needed to apply the certified
functional extension theorem over an arbitrary finite closed base.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso
namespace FiniteClosedFunctionalPartialIso

variable {M N : GraphOn ℕ} {CM CN : ℕ → Finset ℕ}

/-- Transport every member of the complete target value back through
the inverse finite isomorphism. The result is a literal equality of
finite subsets of the original source carrier. -/
theorem completeValue_of_inverse_image
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (y : {v : ℕ // v ∈ p.graph.target}) :
    CM (p.graph.equiv.symm y).val =
      (FiniteC0.namedClosedBaseValue CN p.graph.target y).image
        (fun z => (p.graph.equiv.symm z).val) := by
  classical
  ext x
  constructor
  · intro hx
    have hxS : x ∈ p.graph.source :=
      p.sourceClosed (p.graph.equiv.symm y).val
        (p.graph.equiv.symm y).property hx
    let z : {v : ℕ // v ∈ p.graph.source} := ⟨x, hxS⟩
    let w := p.graph.equiv z
    have hMember : w.val ∈ CN y.val := by
      have h := (p.fullValues (p.graph.equiv.symm y) z).mp hx
      simpa [w] using h
    refine Finset.mem_image.mpr ⟨w, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMember⟩
    · change (p.graph.equiv.symm (p.graph.equiv z)).val = x
      simpa [z] using
        congrArg Subtype.val (p.graph.equiv.symm_apply_apply z)
  · intro hx
    obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
    have hwCN : w.val ∈ CN y.val := (Finset.mem_filter.mp hw).2
    have hEq :
        (p.graph.equiv (p.graph.equiv.symm w)).val = w.val := by simp
    have hEqY :
        (p.graph.equiv (p.graph.equiv.symm y)).val = y.val := by simp
    have hBack :
        (p.graph.equiv.symm w).val ∈
          CM (p.graph.equiv.symm y).val :=
      (p.fullValues (p.graph.equiv.symm y)
        (p.graph.equiv.symm w)).mpr (by simpa [hEq, hEqY] using hwCN)
    exact hwx ▸ hBack

/-- The inverse finite isomorphism as an actual inclusion into a
larger source-side stage, preserving all original natural labels. -/
def inverseStageBaseMap
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (t : Finset ℕ) (ht : p.graph.source ⊆ t) :
    {v : ℕ // v ∈ p.graph.target} → {v : ℕ // v ∈ t} :=
  fun y => ⟨(p.graph.equiv.symm y).val,
    ht (p.graph.equiv.symm y).property⟩

theorem inverseStageBaseMap_injective
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (t : Finset ℕ) (ht : p.graph.source ⊆ t) :
    Function.Injective (inverseStageBaseMap p t ht) := by
  intro x y hxy
  apply (p.graph.equiv.symm).injective
  apply Subtype.ext
  exact congrArg
    (fun z : {v : ℕ // v ∈ t} => z.val) hxy

/-- The inverse-base map reflects every edge and nonedge. -/
theorem inverseStageBaseMap_induced
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (t : Finset ℕ) (ht : p.graph.source ⊆ t)
    (x y : {v : ℕ // v ∈ p.graph.target}) :
    N.adj x.val y.val ↔
      (M.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ)).adj
        (inverseStageBaseMap p t ht x)
        (inverseStageBaseMap p t ht y) := by
  have h := (p.graph.induced (p.graph.equiv.symm x)
    (p.graph.equiv.symm y)).symm
  change N.adj x.val y.val ↔
    M.adj (p.graph.equiv.symm x).val (p.graph.equiv.symm y).val
  simpa only [Equiv.apply_symm_apply] using h

/-- A canonical finite presentation on a stage containing the
source of p has the entire target-base unary value under the
inverse-base embedding. No equality of numerical component
indices is assumed. -/
theorem inverseStageBaseMap_completeValues
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (t : Finset ℕ) (ht : p.graph.source ⊆ t)
    {m : ℕ} (κ : {v : ℕ // v ∈ t} → Fin m)
    (hValues : ∀ x : {v : ℕ // v ∈ t},
      CM x.val =
        (FiniteC0.canonicalValue
          (M.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
          κ x).image (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
    (y : {v : ℕ // v ∈ p.graph.target}) :
    FiniteC0.canonicalValue
      (M.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
      κ (inverseStageBaseMap p t ht y) =
      (FiniteC0.namedClosedBaseValue CN p.graph.target y).image
        (inverseStageBaseMap p t ht) := by
  classical
  let T := {v : ℕ // v ∈ t}
  let f := inverseStageBaseMap p t ht
  apply Finset.image_injective
    (Subtype.val_injective : Function.Injective
      (Subtype.val : T → ℕ))
  calc
    (FiniteC0.canonicalValue
      (M.pullback (Subtype.val : T → ℕ))
      κ (f y)).image (Subtype.val : T → ℕ) =
        CM (p.graph.equiv.symm y).val :=
          (hValues (f y)).symm
    _ = (FiniteC0.namedClosedBaseValue CN p.graph.target y).image
      (fun z => (p.graph.equiv.symm z).val) :=
        completeValue_of_inverse_image p y
    _ = ((FiniteC0.namedClosedBaseValue CN p.graph.target y).image f).image
        (Subtype.val : T → ℕ) := by
          rw [Finset.image_image]
          rfl

end FiniteClosedFunctionalPartialIso
end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
