import BigHrushovski.C0FunctionalFiniteInitialLabels
import BigHrushovski.ForcedGrowth
import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.CanonicalFinNumbering

/-!
# Forcing growth in a finite canonical functional C₀ presentation

A fair Fraïssé construction must grow even when the scheduled
functional request is inapplicable, or its target already lies in
the old stage. The existing strong-graph growth theorem adjoins
an isolated vertex over the empty strong base. The finite
canonical-extension theorem transports the complete old unary
values into this larger finite graph and gives a minimal-component
witness. Relabelling by the old-fixed initial-segment equivalence
gives a new canonical member on Fin m with m > n.

No choice of an arbitrary finite enumerator is made; all old
numerical labels are unchanged. This is one finite successor,
not an infinite functional Fraïssé construction.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every finite canonical functional C₀ member has a strictly
larger canonical finite ordinal extension. It preserves all
complete unary values and has a strong induced copy of the
old member whose numerical labels are fixed pointwise.
The forced fresh vertex is a genuine new point. -/
theorem exists_growingCanonicalFunctionalC0Stage
    {n k : ℕ}
    (S : FiniteFunctionalC0 n k) :
    ∃ (m t : ℕ) (T : FiniteFunctionalC0 m t)
      (f : Fin n → Fin m),
      n < m ∧
      Function.Injective f ∧
      (∀ x : Fin n, (f x).val = x.val) ∧
      (∀ x y : Fin n,
        S.graph.adj x y ↔ T.graph.adj (f x) (f y)) ∧
      (∀ x : Fin n,
        T.unaryValue (f x) = (S.unaryValue x).image f) ∧
      T.graph.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin n)).image f)
        Finset.univ := by
  classical
  let W := FiniteSpan.JointCarrier (Fin n) Unit
  obtain ⟨K, old, fresh, hOldInjective, hOldAdj,
      hSparseK, hOldStrong, hFresh⟩ :=
    FiniteSpan.exists_fresh_strong_extension S.graph S.sparse
  have hOldInduced : ∀ x y : Fin n,
      S.graph.adj x y ↔ K.adj (old x) (old y) :=
    fun x y => (hOldAdj x y).symm
  obtain ⟨t, κ, hSteps, hValues⟩ :=
    FiniteC0.exists_canonical_extension_over_embedding
      S.graph K old hOldInjective hOldInduced S.index
      S.minimal hOldStrong
  obtain ⟨T, label, hFixed, hLabelAdj, hLabelFull, hLabelOld⟩ :=
    exists_initialSegment_canonicalFunctionalExtension
      S.graph K S.index κ hSteps old hOldInjective
      (FiniteSpan.canonicalFinNumbering n) hValues
  let f : Fin n → Fin (Fintype.card W) := label ∘ old
  have hFixedNat : ∀ x : Fin n, (f x).val = x.val := by
    intro x
    calc
      (f x).val = (FiniteSpan.canonicalFinNumbering n x).val :=
        hFixed x
      _ = x.val := FiniteSpan.canonicalFinNumbering_val n x
  have hFreshBeyond : n < Fintype.card W := by
    by_contra hNo
    have hLe : Fintype.card W ≤ n := by omega
    let x : Fin n :=
      ⟨(label fresh).val, lt_of_lt_of_le (label fresh).isLt hLe⟩
    have hEq : label (old x) = label fresh := by
      apply Fin.ext
      calc
        (label (old x)).val = x.val := hFixedNat x
        _ = (label fresh).val := rfl
    have hOldFresh : old x = fresh := label.injective hEq
    exact hFresh
      (Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, hOldFresh⟩)
  have hAdj : ∀ x y : Fin n,
      S.graph.adj x y ↔ T.graph.adj (f x) (f y) := by
    intro x y
    exact (hOldInduced x y).trans (hLabelAdj (old x) (old y))
  have hStrongT : T.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin n)).image f)
      (Finset.univ : Finset (Fin (Fintype.card W))) := by
    have h :=
      (K.strong_image_iff T.graph label label.injective hLabelAdj
        ((Finset.univ : Finset (Fin n)).image old)
        Finset.univ (Finset.subset_univ _)).mpr hOldStrong
    have hUniv :
        (Finset.univ : Finset W).image label =
        (Finset.univ : Finset (Fin (Fintype.card W))) :=
      Finset.image_univ_of_surjective label.surjective
    rw [Finset.image_image, hUniv] at h
    exact h
  refine ⟨Fintype.card W, t, T, f,
    hFreshBeyond, label.injective.comp hOldInjective,
    hFixedNat, hAdj, ?_, hStrongT⟩
  intro x
  exact hLabelOld x

end FiniteCatalogue
end BigHrushovski
