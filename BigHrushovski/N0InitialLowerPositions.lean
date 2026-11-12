import BigHrushovski.N0CanonicalTopOrderFibres
import Mathlib.Data.Finset.Fin
import Mathlib.Tactic

/-!
# Initial lower parts and fixed positions in finite enumerations

A finite local canonical-order fibre fixes every old position, while
the recursive SCC construction naturally specifies an *order* on
the old successor part P. If P is an initial segment in both
complete enumerations, these descriptions agree.

The reason is elementary: the numerical position of a vertex u
equals the number of vertices preceding it. When P is an initial
segment, all predecessors of u in P are themselves in P. Hence
two enumerations with the same order on P give each old vertex
the same numerical position.

This finite order lemma is independent of the orientation and is
the interface between recursive lower-part orderings and
positionwise-fixed canonical local fibres.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of vertices appearing strictly before u in an
actual complete labelled enumeration. -/
noncomputable def orderPredecessors {n : ℕ}
    (e : Fin n ≃ V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => OrderBefore e v u)

theorem mem_orderPredecessors_iff {n : ℕ}
    (e : Fin n ≃ V) (u v : V) :
    v ∈ orderPredecessors e u ↔ OrderBefore e v u := by
  classical
  simp [orderPredecessors]

/-- The index of u in a complete finite enumeration equals the
number of vertices strictly preceding u. This counts all labelled
vertices, independently of the graph relation. -/
theorem enumerationPosition_eq_card_predecessors {n : ℕ}
    (e : Fin n ≃ V) (u : V) :
    (e.symm u).val = (orderPredecessors e u).card := by
  classical
  let j : Fin n := e.symm u
  let indices : Finset (Fin n) :=
    (Finset.range j.val).attachFin (by
      intro m hm
      exact lt_trans (Finset.mem_range.mp hm) j.isLt)
  have hIndices (i : Fin n) : i ∈ indices ↔ i < j := by
    simp only [indices, Finset.mem_attachFin, Finset.mem_range, Fin.lt_def]
  have hIndicesCard : indices.card = j.val := by
    simp [indices]
  have hImage :
      indices.image e = orderPredecessors e u := by
    ext v
    simp only [Finset.mem_image, mem_orderPredecessors_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hij : i < j := (hIndices i).mp hi
      simpa [OrderBefore, j] using hij
    · intro hv
      refine ⟨e.symm v, (hIndices (e.symm v)).mpr ?_, ?_⟩
      · simpa [OrderBefore, j] using hv
      · simp
  have hCardImage : (indices.image e).card = indices.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact e.injective hab
  calc
    (e.symm u).val = indices.card := hIndicesCard.symm
    _ = (indices.image e).card := hCardImage.symm
    _ = (orderPredecessors e u).card :=
      congrArg Finset.card hImage

/-- If P is an initial segment in both enumerations and all
pairwise comparisons within P agree, then the complete
enumerations place every vertex of P at the same *absolute*
ordinal position. -/
theorem sameLowerPositions_of_initial_and_oldOrder
    (P : Finset V) {n : ℕ}
    (e f : Fin n ≃ V)
    (heInitial : IsLowerBeforeRest P e)
    (hfInitial : IsLowerBeforeRest P f)
    (hOrder : ∀ u ∈ P, ∀ v ∈ P,
      (OrderBefore e u v ↔ OrderBefore f u v)) :
    SameLowerPositions P e f := by
  have hPred (u : V) (hu : u ∈ P) :
      orderPredecessors e u = orderPredecessors f u := by
    ext v
    simp only [mem_orderPredecessors_iff]
    by_cases hv : v ∈ P
    · exact hOrder v hv u hu
    · have hNotE : ¬ OrderBefore e v u := by
        intro h
        exact lt_asymm (heInitial u v hu hv) h
      have hNotF : ¬ OrderBefore f v u := by
        intro h
        exact lt_asymm (hfInitial u v hu hv) h
      exact ⟨(fun h => (hNotE h).elim),
        (fun h => (hNotF h).elim)⟩
  have hPos (u : V) (hu : u ∈ P) :
      e.symm u = f.symm u := by
    apply Fin.ext
    calc
      (e.symm u).val = (orderPredecessors e u).card :=
        enumerationPosition_eq_card_predecessors e u
      _ = (orderPredecessors f u).card := by
        rw [hPred u hu]
      _ = (f.symm u).val :=
        (enumerationPosition_eq_card_predecessors f u).symm
  intro i hi
  have h := congrArg f (hPos (e i) hi)
  have hfi : f i = e i := by
    simpa using h
  exact hfi

/-- For two enumerations in which P is an initial segment,
fixing its old positions is *equivalent* to preserving every
comparison between old vertices. -/
theorem sameLowerPositions_iff_oldOrder_of_initial
    (P : Finset V) {n : ℕ}
    (e f : Fin n ≃ V)
    (heInitial : IsLowerBeforeRest P e)
    (hfInitial : IsLowerBeforeRest P f) :
    SameLowerPositions P e f ↔
      ∀ u ∈ P, ∀ v ∈ P,
        (OrderBefore e u v ↔ OrderBefore f u v) := by
  constructor
  · intro h u hu v hv
    exact sameLowerPositions_preserves_old_order P e f h hu hv
  · intro h
    exact sameLowerPositions_of_initial_and_oldOrder
      P e f heInitial hfInitial h

end FiniteOrientation
end BigHrushovski
