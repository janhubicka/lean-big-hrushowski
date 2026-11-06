import BigHrushovski.HrushovskiEllentuckCFBirthSupport
import BigHrushovski.CFBirthGeneratedTransport

/-!
# Forward range formula for C_F level embeddings

The first half of the manuscript's exact range equation is independent
of unique level lifting. A map preserving *complete* generated closures
and transforming the level of every vertex by h carries every finite
generated level support exactly to its h-image. Consequently its range
is contained in the complete-support domain over the range of h.

We then instantiate this result in the actual countable C_F birth
presentation, using the existing verified complete b-value transport
lemma. The *reverse* range inclusion is the finite inverse-lifting
argument and remains an independent Track B obligation.
-/

namespace BigHrushovski.Ellentuck

universe u v

variable {Vertex : Type u} {Level : Type v}
-- Finset.image needs decidable equality on its target. The typeclass
-- assumptions are computational only and are available classically.
variable [DecidableEq Vertex] [DecidableEq Level]

/-- Exact transport of complete finite level supports. This is stronger
than preserving the levels of individual vertices. -/
theorem generatedSupport_image
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (f : Vertex → Vertex) (h : Level → Level)
    (hΓ : ∀ v, (Γ v).image f = Γ (f v))
    (hπ : ∀ v, π (f v) = h (π v))
    (v : Vertex) :
    (generatedSupport Γ π v).image h =
      generatedSupport Γ π (f v) := by
  classical
  change ((Γ v).image π).image h = (Γ (f v)).image π
  rw [← hΓ v]
  simp only [Finset.image_image]
  congr 1
  funext w
  exact (hπ w).symm

/-- The unconditional forward inclusion of the expected copy-range
formula, assuming only exact preservation of full closures and a level
map h. No uniqueness, surjectivity or inverse level lifting is used. -/
theorem image_subset_supportDomain
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (f : Vertex → Vertex) (h : Level → Level)
    (hΓ : ∀ v, (Γ v).image f = Γ (f v))
    (hπ : ∀ v, π (f v) = h (π v)) :
    (Set.range f : Set Vertex) ⊆
      supportDomain (generatedSupport Γ π) (Set.range h) := by
  rintro w ⟨v, rfl⟩
  intro q hq
  have hmem : q ∈ (generatedSupport Γ π v).image h := by
    rw [generatedSupport_image Γ π f h hΓ hπ v]
    exact hq
  rcases Finset.mem_image.mp hmem with ⟨p, _, hpq⟩
  exact ⟨p, hpq⟩

end BigHrushovski.Ellentuck

namespace BigHrushovski
namespace CFCoherentTower

/-- In the actual birth structure, preserving all complete b-values
already preserves the full one-generated b-closures. -/
theorem birthSingletonClosure_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (v : Vertex F K) :
    (birthSingletonClosure F K v).image f =
      birthSingletonClosure F K (f v) := by
  have hClosure :=
    birthGeneratedClosure_image_of_bValues F K f
      ({v} : Finset (Vertex F K))
      (fun w _ => hB w)
  simpa only [birthSingletonClosure, Finset.image_singleton] using hClosure

/-- Exact transport of *complete* birth-level supports for a
b-preserving map whose level action is h. -/
theorem birthLevelSupport_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) (h : ℕ → ℕ)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1)
    (v : Vertex F K) :
    (birthLevelSupport F K v).image h =
      birthLevelSupport F K (f v) := by
  classical
  exact Ellentuck.generatedSupport_image
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    f h
    (birthSingletonClosure_image_of_bValues F K f hB)
    hBirth v

/-- The forward half of the full range formula on the literal
countable C_F presentation. The reverse inclusion still needs finite
unique inverse level lifting and is not asserted here. -/
theorem birthEmbedding_range_subset_levelDomain
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) (h : ℕ → ℕ)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1) :
    (Set.range f : Set (Vertex F K)) ⊆
      birthLevelDomain F K (Set.range h) := by
  classical
  exact Ellentuck.image_subset_supportDomain
    (birthSingletonClosure F K)
    (fun x : Vertex F K => x.1)
    f h
    (birthSingletonClosure_image_of_bValues F K f hB)
    hBirth

end CFCoherentTower
end BigHrushovski
