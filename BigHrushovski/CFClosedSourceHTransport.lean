import BigHrushovski.FiniteRestrictedHullTransport
import BigHrushovski.CFBirthFirstOrder

/-!
# Transport H-values on arbitrary closed C_F source subsets

A b-embedding of a closed C_F substructure is defined only on that
substructure. It need not extend to a globally induced embedding of
the whole countable birth carrier.

We therefore let X be an arbitrary possibly infinite b-closed
vertex subset and impose inducedness, injectivity and exact b-value
preservation only for vertices of X. A map outside X is irrelevant.

For each finite S⊆X, its finite generated b-closure T lies in X
and is globally strictly d-closed. Exact b-value preservation
makes f[T] b-closed as well. The reusable restricted-embedding
d-hull theorem transports the finite hull between T and f[T]
without assuming anything about f outside T. Global finite-hull
leastness then identifies both hulls with the H-values.

This is the missing local H-value preservation needed for
embeddings of arbitrary closed substructures. The complete
embedding equivalence still requires root/order transport and
its converse on the same restricted source.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Full finite b-generated closure is carried onto the target
closure, assuming preservation of complete b-values only on an
arbitrary b-closed source set X. No total-structure preservation
outside X is used. -/
theorem birthGeneratedClosure_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (s : Finset (Vertex F K))
    (hsX : ∀ v ∈ s, v ∈ X) :
    (birthGeneratedClosure F K s).image f =
      birthGeneratedClosure F K (s.image f) := by
  have hCX : ∀ v ∈ birthGeneratedClosure F K s, v ∈ X :=
    generatedClosure_subset_closedSet F K X hX s hsX
  exact birthGeneratedClosure_image_of_bValues F K f s
    (fun v hv => hB v (hCX v hv))

/-- Complete H-values are preserved on every finite subset of an
arbitrary b-closed source set. The finite inducedness and local
injectivity assumptions are restricted to X; the map may
behave arbitrarily outside X.

In particular the theorem applies to the defined H-values on
finite sets consisting of first vertices, without enlarging the
language domain of that partial operation. -/
theorem birthDClosedHull_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (s : Finset (Vertex F K))
    (hsX : ∀ v ∈ s, v ∈ X) :
    (birthDClosedHull F K s).image f =
      birthDClosedHull F K (s.image f) := by
  classical
  let G := countableGraph F K
  let d := G.toPredimension
  let T := birthGeneratedClosure F K s
  have hTclosed : IsBirthBlockClosed F K T :=
    birthGeneratedClosure_closed F K s
  have hTsubX : ∀ v ∈ T, v ∈ X :=
    generatedClosure_subset_closedSet F K X hX s hsX
  have hBOn : ∀ v ∈ T,
      (birthBValue F K v).image f = birthBValue F K (f v) := by
    intro v hv
    exact hB v (hTsubX v hv)
  have hTImgClosed : IsBirthBlockClosed F K (T.image f) :=
    birthBlockClosed_image_of_bValues F K f T hTclosed hBOn
  have hSrcGlobal : d.IsGloballyDClosed T :=
    birthBlockClosed_global_dClosed F K T hTclosed
  have hTgtGlobal : d.IsGloballyDClosed (T.image f) :=
    birthBlockClosed_global_dClosed F K (T.image f) hTImgClosed
  have hsT : s ⊆ T :=
    birthGeneratedClosure_contains F K s
  have hSrc :
      birthDClosedHull F K s = d.dClosedHull s T :=
    d.globalDClosedHull_eq_closedContainer
      (birthDClosedChain F K) s T hsT hSrcGlobal
  have hTgt :
      birthDClosedHull F K (s.image f) =
        d.dClosedHull (s.image f) (T.image f) :=
    d.globalDClosedHull_eq_closedContainer
      (birthDClosedChain F K) (s.image f) (T.image f)
      (Finset.image_mono f hsT) hTgtGlobal
  have hfT : ∀ u ∈ T, ∀ v ∈ T, f u = f v → u = v := by
    intro u hu v hv huv
    exact hf u (hTsubX u hu) v (hTsubX v hv) huv
  have hAdjT : ∀ u ∈ T, ∀ v ∈ T,
      G.adj u v ↔ G.adj (f u) (f v) := by
    intro u hu v hv
    exact hAdj u (hTsubX u hu) v (hTsubX v hv)
  calc
    (birthDClosedHull F K s).image f =
        (d.dClosedHull s T).image f := congrArg (Finset.image f) hSrc
    _ = d.dClosedHull (s.image f) (T.image f) :=
      G.dClosedHull_image_on G f T hfT hAdjT s hsT
    _ = birthDClosedHull F K (s.image f) := hTgt.symm

end CFCoherentTower
end BigHrushovski
