import BigHrushovski.CFArbitraryMinimalResponse
import BigHrushovski.CFPrescribedSourceLift

/-!
# Realize any minimal strict C_F extension over a prescribed countable copy

The full finite one-step response has now been proved for an actual
d-closed source inside some finite tagged stage. We remove this
remaining stage-level input.

Given a prescribed induced embedding e:S→M_F^dagger whose image is
globally strictly d-closed, the certified source-lift theorem
places e pointwise inside one actual finite stage U_n, giving an
induced f:S→U_n with d-closed image and birth_n∘f=e.
The canonical support, local growth and exact-support certificates
and a bounded named request are constructed by the finite
arbitraryMinimalCF_globalResponse theorem. Composing the response
with birth_n∘f=e realizes the desired minimal extension while
fixing the original countable embedding literally.

No pre-normalized local type, selected request, or new-vertex map
is included in the hypotheses. The remaining standing inputs are
membership of the requested finite graph in C_F, its minimal
strict d-closedness, and the numerical inverse property of the
chosen growth-size bound K. These hold in the published C_F
class for the generalized inverse of its monotone unbounded F.

The finite-chain induction will extend this one-step property to
arbitrary finite strict d-closed extensions. This theorem does
not yet assert the full Fraïssé identification or properties of
the later functional R,H presentation.
-/

namespace BigHrushovski
namespace CFCoherentTower

variable {S B : Type*} [Fintype S] [DecidableEq S]
  [Fintype B] [DecidableEq B] [LinearOrder B]

/-- Every requested finite minimal strict C_F extension is
realized over an *arbitrary prescribed* globally strictly
d-closed copy of its old part in the countable birth graph.

The extension is induced, including all nonedges, and its
entire image is again globally strictly d-closed. -/
theorem minimalCF_extension_over_global_copy
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k m : ℕ,
      F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k)
    (H : GraphOn (Sum S B))
    (hMinimal : H.toPredimension.IsMinimalDClosedStep
      (CFLocalCatalogue.actualOld S B) Finset.univ)
    (hGrowth : H.IsGrowthSparse F Finset.univ)
    (e : S → Vertex F K) (he : Function.Injective e)
    (hAdj : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (countableGraph F K).adj (e x) (e y))
    (hOldClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset S).image e)) :
    ∃ g : Sum S (Fin (Fintype.card B)) → Vertex F K,
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) = e x) ∧
      (∀ x y : Sum S (Fin (Fintype.card B)),
        (H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (CFLocalCatalogue.increasingNewBlock (B := B)).toEquiv)).adj x y ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin (Fintype.card B)))).image g) := by
  classical
  let A : GraphOn S := H.pullback Sum.inl
  have hOldAdj : ∀ x y : S,
      A.adj x y ↔ (countableGraph F K).adj (e x) (e y) := hAdj
  obtain ⟨n, f, hf, hfAdj, hfOld, hfClosed⟩ :=
    prescribedClosedSource_liftToStage F K A e he
      hOldAdj hOldClosed
  have hOldStage : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage F K n).graph.adj (f x) (f y) := hfAdj
  obtain ⟨g, hgInj, hgOld, hgAdj, hgClosed⟩ :=
    arbitraryMinimalCF_globalResponse F K hInverse n
      H hMinimal hGrowth f hf hOldStage hfClosed
  refine ⟨g, hgInj, ?_, hgAdj, hgClosed⟩
  intro x
  exact (hgOld x).trans (hfOld x)

end CFCoherentTower
end BigHrushovski
