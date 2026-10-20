import BigHrushovski.CFBirthHullNaturality
import BigHrushovski.CFBirthSupportRecovery
import BigHrushovski.CFBirthRootRecovery

/-!
# Complete auxiliary b-values and their induced images

The auxiliary set-valued unary operation b(v) in the C_F manuscript
has one complete value: the literal tagged fresh block of v together
with its complete old support. We package this value once, and prove
that closure under all complete b-values is exactly the established
birth-block/support closure predicate.

An induced injection which preserves complete b-values maps every
finite b-closed subset to a finite b-closed subset. Together with
the separately verified closed-container hull naturality, this
proves exact H-value transport on all finite subsets of the domain.

This is the b-to-H-value portion of functional embedding equivalence.
The chosen first vertices of blocks and reflection of partial H
domains still require preservation of the order and level structure.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The *complete* auxiliary b(v), not merely the graph neighbours
of v or the block containing v. Its support is the literally
named old d-closed support of the actual request. -/
noncomputable def birthBValue
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Vertex F K → Finset (Vertex F K)
  | ⟨n, ⟨r, _⟩⟩ => birthSupport F K n r ∪ birthBlock F K n r

theorem birthBValue_of_fresh
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val) :
    birthBValue F K (⟨n, ⟨r, i⟩⟩ : Vertex F K) =
      birthSupport F K n r ∪ birthBlock F K n r :=
  rfl

/-- Saturation of one selected block forces every vertex of
that complete tagged fresh block into the finite closed set. -/
theorem birthBlock_subset_closed_of_fresh
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    birthBlock F K n r ⊆ s := by
  classical
  intro v hv
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
  obtain ⟨j, _, hjw⟩ := Finset.mem_image.mp hw
  have hV : v = (⟨n, ⟨r, j⟩⟩ : Vertex F K) := by
    calc
      v = toVertex F K (n + 1) w := hwv.symm
      _ = toVertex F K (n + 1) (Sum.inr ⟨r, j⟩) := by rw [hjw]
      _ = (⟨n, ⟨r, j⟩⟩ : Vertex F K) := rfl
  rw [hV]
  exact (hs n r i hi).1 j

/-- Any finite b-closed set containing v contains every vertex
of the entire auxiliary value b(v). -/
theorem birthBValue_subset_of_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    {v : Vertex F K} (hv : v ∈ s) :
    birthBValue F K v ⊆ s := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  intro w hw
  change w ∈ birthSupport F K n r ∪ birthBlock F K n r at hw
  rcases Finset.mem_union.mp hw with hSupp | hFresh
  · exact birthSupport_subset_closed_of_fresh F K s hs n r i hv hSupp
  · exact birthBlock_subset_closed_of_fresh F K s hs n r i hv hFresh

/-- The previously defined finite block-closure predicate is
equivalent to closure under each *complete* auxiliary b-value. -/
theorem birthBlockClosed_iff_bValue_subset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    IsBirthBlockClosed F K s ↔
      ∀ v ∈ s, birthBValue F K v ⊆ s := by
  constructor
  · intro hs v hv
    exact birthBValue_subset_of_closed F K s hs hv
  · intro hSub
    intro n r i hi
    have hValue :
        birthBValue F K (⟨n, ⟨r, i⟩⟩ : Vertex F K) ⊆ s :=
      hSub _ hi
    constructor
    · intro j
      apply hValue
      exact Finset.mem_union.mpr
        (Or.inr (birthFresh_mem_block F K n r j))
    · intro u hu
      apply hValue
      exact Finset.mem_union.mpr
        (Or.inl (birthSupport_mem_of_old F K n r u hu))

/-- A complete b-value preserving map sends a closed finite
set to a closed finite set. Injectivity is not needed for this
algebraic assertion, provided all b-values are mapped *onto*
the corresponding complete target values. -/
theorem birthBlockClosed_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (hfB : ∀ v ∈ s,
      (birthBValue F K v).image f = birthBValue F K (f v)) :
    IsBirthBlockClosed F K (s.image f) := by
  apply (birthBlockClosed_iff_bValue_subset F K (s.image f)).mpr
  intro w hw
  obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
  have hSub : birthBValue F K v ⊆ s :=
    birthBValue_subset_of_closed F K s hs hv
  have hImageSub :
      (birthBValue F K v).image f ⊆ s.image f :=
    Finset.image_mono f hSub
  rw [hfB v hv] at hImageSub
  simpa only [hvw] using hImageSub

/-- Complete preservation of the auxiliary b-values gives
exact transport of global d-hulls on finite subsets, without
an independent closed-image hypothesis. -/
theorem birthDClosedHull_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (s t : Finset (Vertex F K))
    (hst : s ⊆ t)
    (ht : IsBirthBlockClosed F K t)
    (hfB : ∀ v ∈ t,
      (birthBValue F K v).image f = birthBValue F K (f v)) :
    (birthDClosedHull F K s).image f =
      birthDClosedHull F K (s.image f) :=
  birthDClosedHull_image_of_closedContainer F K f hf hAdj
    s t hst ht (birthBlockClosed_image_of_bValues F K f t ht hfB)

end CFCoherentTower
end BigHrushovski
