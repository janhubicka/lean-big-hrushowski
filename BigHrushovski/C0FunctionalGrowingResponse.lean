import BigHrushovski.C0FunctionalFiniteOrdinalResponse
import BigHrushovski.C0FunctionalForcedGrowth

/-!
# A strictly growing labelled finite canonical C₀ response

The finite functional response can have the same number of
vertices as the old stage when its target was already realized.
The independent forced-growth theorem then appends an isolated
strong component, preserving *all* already assigned complete
unary function values and every old numerical coordinate.

Composing these two certified finite steps gives a strictly
growing finite canonical functional response to every
applicable labelled functional request. Both the original
old graph and the requested target embed as induced strong
subgraphs, their complete unary functions are preserved
exactly, and their two source maps agree pointwise.

This is the remaining finite successor interface for the
countable fair functional recursion. It does not by itself
construct the coherent countable sequence or its limit.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A single functional request can always be answered *and*
the finite stage made strictly larger. The canonical old
numeric labels stay fixed, the entire old unary operation
is preserved and the target has an induced strong functional
copy over the prescribed source map. -/
theorem exists_growingFiniteOrdinalFunctionalResponse
    {a p b q c r : ℕ}
    (S : FiniteFunctionalC0 a p)
    (D : FunctionalC0Diagram b q c r)
    (e : Fin b → Fin a)
    (he : Function.Injective e)
    (hInd : ∀ x y : Fin b,
      D.source.graph.adj x y ↔ S.graph.adj (e x) (e y))
    (hValues : ∀ x : Fin b,
      S.unaryValue (e x) =
        (D.source.unaryValue x).image e) :
    ∃ (m t : ℕ)
      (T : FiniteFunctionalC0 m t)
      (old : Fin a → Fin m)
      (target : Fin c → Fin m),
      a < m ∧
      Function.Injective old ∧ Function.Injective target ∧
      (∀ x : Fin a, (old x).val = x.val) ∧
      (∀ x y : Fin a,
        S.graph.adj x y ↔ T.graph.adj (old x) (old y)) ∧
      (∀ x y : Fin c,
        D.target.graph.adj x y ↔
          T.graph.adj (target x) (target y)) ∧
      (∀ x : Fin a,
        T.unaryValue (old x) = (S.unaryValue x).image old) ∧
      (∀ x : Fin c,
        T.unaryValue (target x) =
          (D.target.unaryValue x).image target) ∧
      (∀ x : Fin b,
        old (e x) = target (D.embedding x)) ∧
      T.graph.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin a)).image old)
        Finset.univ ∧
      T.graph.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin c)).image target)
        Finset.univ := by
  classical
  obtain ⟨size, k, M, f, g, hf, hg, hFixed, hAdjF,
      hAdjG, hValF, hValG, hBase, hStrongF, hStrongG⟩ :=
    exists_finiteOrdinalFunctionalResponse S D e he hInd hValues
  obtain ⟨m, t, T, u, hGrow, hu, hFixedU, hAdjU,
      hValU, hStrongU⟩ :=
    exists_growingCanonicalFunctionalC0Stage M
  let old : Fin a → Fin m := u ∘ f
  let target : Fin c → Fin m := u ∘ g
  have hSizeLower : a ≤ size := by
    by_contra hn
    have hn' : size < a := by omega
    let x : Fin a := ⟨size, hn'⟩
    have hLabel : (f x).val = size := hFixed x
    exact (Nat.ne_of_lt (f x).isLt) hLabel
  have hStrict : a < m := lt_of_le_of_lt hSizeLower hGrow
  have hFixedOld : ∀ x : Fin a, (old x).val = x.val := by
    intro x
    calc
      (old x).val = (f x).val := hFixedU (f x)
      _ = x.val := hFixed x
  have hAdjOld : ∀ x y : Fin a,
      S.graph.adj x y ↔ T.graph.adj (old x) (old y) := by
    intro x y
    exact (hAdjF x y).trans (hAdjU (f x) (f y))
  have hAdjTarget : ∀ x y : Fin c,
      D.target.graph.adj x y ↔
        T.graph.adj (target x) (target y) := by
    intro x y
    exact (hAdjG x y).trans (hAdjU (g x) (g y))
  have hFullOld : ∀ x : Fin a,
      T.unaryValue (old x) = (S.unaryValue x).image old := by
    intro x
    calc
      T.unaryValue (old x) =
          (M.unaryValue (f x)).image u := hValU (f x)
      _ = ((S.unaryValue x).image f).image u := by
        rw [hValF x]
      _ = (S.unaryValue x).image old := by
        rw [Finset.image_image]
  have hFullTarget : ∀ x : Fin c,
      T.unaryValue (target x) =
        (D.target.unaryValue x).image target := by
    intro x
    calc
      T.unaryValue (target x) =
          (M.unaryValue (g x)).image u := hValU (g x)
      _ = ((D.target.unaryValue x).image g).image u := by
        rw [hValG x]
      _ = (D.target.unaryValue x).image target := by
        rw [Finset.image_image]
  have hOldStrongT : T.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin a)).image old)
      (Finset.univ : Finset (Fin m)) := by
    have hLift :=
      (M.graph.strong_image_iff T.graph u hu hAdjU
        ((Finset.univ : Finset (Fin a)).image f)
        Finset.univ (Finset.subset_univ _)).mpr hStrongF
    have hTotal : T.graph.toPredimension.IsStrong
        (((Finset.univ : Finset (Fin a)).image f).image u)
        (Finset.univ : Finset (Fin m)) :=
      T.graph.toPredimension.strong_trans hLift hStrongU
    rw [Finset.image_image] at hTotal
    exact hTotal
  have hTargetStrongT : T.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin c)).image target)
      (Finset.univ : Finset (Fin m)) := by
    have hLift :=
      (M.graph.strong_image_iff T.graph u hu hAdjU
        ((Finset.univ : Finset (Fin c)).image g)
        Finset.univ (Finset.subset_univ _)).mpr hStrongG
    have hTotal : T.graph.toPredimension.IsStrong
        (((Finset.univ : Finset (Fin c)).image g).image u)
        (Finset.univ : Finset (Fin m)) :=
      T.graph.toPredimension.strong_trans hLift hStrongU
    rw [Finset.image_image] at hTotal
    exact hTotal
  refine ⟨m, t, T, old, target, hStrict, hu.comp hf,
    hu.comp hg, hFixedOld, hAdjOld, hAdjTarget,
    hFullOld, hFullTarget, ?_, hOldStrongT, hTargetStrongT⟩
  intro x
  exact congrArg u (hBase x)

end FiniteCatalogue
end BigHrushovski
