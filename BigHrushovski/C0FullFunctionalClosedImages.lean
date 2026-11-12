import BigHrushovski.C0CountableIntrinsicComponents
import BigHrushovski.C0FiniteEquivTransport

/-!
# Track A: the image of a complete functional embedding is closed

Suppose a finite functional structure with unary operation D embeds
into a countable C₀ structure with complete unary operation C, and
the embedding preserves the entire set-valued unary function by
equality of finite images. Then its image is automatically C-closed.

If the countable structure has cofinal exact canonical finite stages,
the image is consequently globally strong in the graph reduct.
Complete values also give precise reflection of unary membership
under an injective embedding. These are the finite-image facts needed
by the closed functional back-and-forth argument.
-/

namespace BigHrushovski
namespace FiniteC0

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The image of a finite full-functional embedding is closed
under every member of the complete target unary value. This does
not follow from graph inducedness alone. -/
theorem fullFunctionalImage_closed
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (D : U → Finset U) (f : U → ℕ)
    (hValues : ∀ u : U, C (f u) = (D u).image f) :
    N.IsClosedUnderValues C
      ((Finset.univ : Finset U).image f) := by
  classical
  intro x hx y hy
  obtain ⟨u, _, hux⟩ := Finset.mem_image.mp hx
  have hCy : y ∈ C (f u) := by
    rw [hux]
    exact hy
  rw [hValues u] at hCy
  obtain ⟨v, _, hvy⟩ := Finset.mem_image.mp hCy
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hvy⟩

/-- An injective complete-functional embedding preserves and
reflects membership in the entire unary value, not merely its
induced restriction to the source domain. -/
theorem fullFunctionalImage_mem_iff
    (C : ℕ → Finset ℕ) (D : U → Finset U)
    (f : U → ℕ) (hf : Function.Injective f)
    (hValues : ∀ u : U, C (f u) = (D u).image f)
    (x y : U) :
    f y ∈ C (f x) ↔ y ∈ D x := by
  classical
  rw [hValues x]
  constructor
  · intro h
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
    have hzy : z = y := hf heq
    simpa [hzy] using hz
  · intro h
    exact Finset.mem_image.mpr ⟨y, h, rfl⟩

/-- The induced graph on the exact finite image of an injected
map has precisely the source adjacency relation whenever the
original embedding preserves and reflects all edges. -/
theorem fullFunctionalImage_induced
    (G : GraphOn U) (N : GraphOn ℕ)
    (f : U → ℕ) (hf : Function.Injective f)
    (hAdj : ∀ u v : U, G.adj u v ↔ N.adj (f u) (f v))
    (u v : U) :
    G.adj u v ↔
      (N.pullback (Subtype.val :
        {w : ℕ // w ∈ (Finset.univ : Finset U).image f} → ℕ)).adj
        (imageCarrierEquiv f hf u)
        (imageCarrierEquiv f hf v) := by
  exact hAdj u v

/-- In a countable canonical C₀ graph, a finite complete-functional
image is not only closed but globally strong, with no extra
strongness hypothesis on the embedding. -/
theorem canonicalStages_fullFunctionalImage_globalStrong
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (D : U → Finset U) (f : U → ℕ)
    (hValues : ∀ u : U, C (f u) = (D u).image f) :
    N.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset U).image f) := by
  exact canonicalStages_closed_globalStrong N C stage hCover hStage
    ((Finset.univ : Finset U).image f)
    (fullFunctionalImage_closed N C D f hValues)

end FiniteC0
end BigHrushovski
