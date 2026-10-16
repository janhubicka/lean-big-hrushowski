import BigHrushovski.CFPrescribedSourceLift
import BigHrushovski.CFCountableResponse
import BigHrushovski.CFDClosedTransport

/-!
# The actual named support of a prescribed finite C_F source

The countable construction responds to local types over literal
d-closed supports in one finite tagged stage. If a prescribed
finite source S has been lifted into that stage as an induced
d-closed image, then every d-closed support P in S has a
strictly d-closed *literal* image Q=f[P] in the entire stage.

The proof is just exact induced-image transport of the finite
interval P <=d S, followed by transitivity with the given
d-closed image of S. Its role in the genericity proof is to
avoid exchanging Q for an abstract isomorphic copy of P.

The resulting Q also remains globally d-closed in the
countable birth graph, because the stage itself is globally
d-closed there. This result is independent of the growth
function and of the numerical fresh-block bound K.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- An actual d-closed support of a finite induced source,
carried by its *prescribed* embedding into a tagged stage,
remains d-closed in the entire tagged stage. -/
theorem inducedSource_namedSupport_dClosed
    {S : Type*} [Fintype S] [DecidableEq S]
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (A : GraphOn S)
    (f : S → (stage F K n).carrier)
    (hf : Function.Injective f)
    (hAdj : ∀ x y : S,
      A.adj x y ↔ (stage F K n).graph.adj (f x) (f y))
    (hImage : (stage F K n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ)
    (P : Finset S)
    (hP : A.toPredimension.IsDClosed P Finset.univ) :
    (stage F K n).graph.toPredimension.IsDClosed
      (P.image f) Finset.univ := by
  classical
  have hRel :
      (stage F K n).graph.toPredimension.IsDClosed
        (P.image f)
        ((Finset.univ : Finset S).image f) :=
    (A.dClosed_image_iff
      (stage F K n).graph f hf hAdj P Finset.univ
      (Finset.subset_univ _)).mpr hP
  exact (stage F K n).graph.toPredimension.dclosed_trans hRel hImage

/-- The same support, with exactly the same vertex names,
is globally strictly d-closed in the countable birth graph. -/
theorem inducedSource_namedSupport_global
    {S : Type*} [Fintype S] [DecidableEq S]
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (A : GraphOn S)
    (f : S → (stage F K n).carrier)
    (hf : Function.Injective f)
    (hAdj : ∀ x y : S,
      A.adj x y ↔ (stage F K n).graph.adj (f x) (f y))
    (hImage : (stage F K n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ)
    (P : Finset S)
    (hP : A.toPredimension.IsDClosed P Finset.univ) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      ((P.image f).image (toVertex F K n)) := by
  exact finiteClosedPart_global F K n (P.image f)
    (inducedSource_namedSupport_dClosed F K n A f hf
      hAdj hImage P hP)

/-- The named support is contained in the prescribed old source
without introducing any vertices outside its given image. -/
theorem inducedSource_namedSupport_subset
    {S U : Type*} [DecidableEq S] [Fintype S] [DecidableEq U]
    (f : S → U) (P : Finset S) :
    P.image f ⊆ (Finset.univ : Finset S).image f :=
  Finset.image_mono f (Finset.subset_univ _)

end CFCoherentTower
end BigHrushovski
