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
the missing interface between recursive lower-part orderings and
positionwise-fixed canonical local fibres.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The index of u in a complete finite enumeration equals the
number of vertices strictly preceding u. This counts all labelled
vertices, independently of the graph relation. -/
theorem enumerationPosition_eq_card_predecessors {n : ℕ}
    (e : Fin n ≃ V) (u : V) :
    (e.symm u).val =
      ((Finset.univ : Finset V).filter
        (fun v => OrderBefore e v u)).card := by
  classical
  let j : Fin n := e.symm u
  let prefix : Finset (Fin n) :=
    (Finset.range j.val).attachFin (by
      intro m hm
      exact lt_trans (Finset.mem_range.mp hm) j.isLt)
  have hPrefix (i : Fin n) : i ∈ prefix ↔ i < j := by
    simp [prefix, Fin.lt_def]
  have hPrefixCard : prefix.card = j.val := by
    simp [prefix]
  have hImage :
      prefix.image e =
        (Finset.univ : Finset V).filter
          (fun v => OrderBefore e v u) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hij : i < j := (hPrefix i).mp hi
      simpa [OrderBefore, j] using hij
    · intro hv
      refine ⟨e.symm v, (hPrefix (e.symm v)).mpr ?_, ?_⟩
      · simpa [OrderBefore, j] using hv
      · simp
  have hCardImage : (prefix.image e).card = prefix.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact e.injective hab
  calc
    (e.symm u).val = prefix.card := hPrefixCard.symm
    _ = (prefix.image e).card := hCardImage.symm
    _ = ((Finset.univ : Finset V).filter
          (fun v => OrderBefore e v u)).card :=
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
      ((Finset.univ : Finset V).filter
        (fun v => OrderBefore e v u)) =
      ((Finset.univ : Finset V).filter
        (fun v => OrderBefore f v u)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
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
      (e.symm u).val = ((Finset.univ : Finset V).filter
          (fun v => OrderBefore e v u)).card :=
        enumerationPosition_eq_card_predecessors e u
      _ = ((Finset.univ : Finset V).filter
          (fun v => OrderBefore f v u)).card := by
        rw [hPred u hu]
      _ = (f.symm u).val :=
        (enumerationPosition_eq_card_predecessors f u).symm
  intro i hi
  have h := congrArg f (hPos (e i) hi)
  have hfi : f i = e i := by
    simpa using h
  exact hfi.symm

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
