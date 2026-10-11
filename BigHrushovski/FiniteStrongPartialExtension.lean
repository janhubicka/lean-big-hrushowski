import BigHrushovski.FiniteStrongPartialIso
import BigHrushovski.FiniteImageEquiv

/-!
# Packing a finite strong embedding into a strong partial isomorphism

A finite strong forth step supplies an induced injective map from a
finite globally strong source container into the other graph, with
globally strong finite image. To iterate forth/back, we must turn
this map into an actual finite strong partial isomorphism whose
source is the chosen container and target is the exact finite image.

The finite-image equivalence fixes the numeric value of every
source vertex, so the resulting partial isomorphism extends the
old one pointwise without any fresh enumeration or hidden relabelling.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- Package an induced, globally strong finite response embedding as
a strong finite partial isomorphism over the literal image of g,
retaining every value of the previous strong partial isomorphism. -/
theorem exists_extension_from_image
    (p : FiniteStrongPartialIso M N)
    (c : Finset ℕ) (hac : p.source ⊆ c)
    (hc : M.toPredimension.IsGloballyStrong c)
    (g : {x : ℕ // x ∈ c} → ℕ)
    (hg : Function.Injective g)
    (hIndG : ∀ x y : {x : ℕ // x ∈ c},
      M.adj x.val y.val ↔ N.adj (g x) (g y))
    (hBase : ∀ x : {x : ℕ // x ∈ p.source},
      g ⟨x.val, hac x.property⟩ = (p.equiv x).val)
    (hGlobalG : N.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset {x : ℕ // x ∈ c}).image g)) :
    ∃ (q : FiniteStrongPartialIso M N)
        (hs : p.source ⊆ q.source),
      q.source = c ∧
      q.target =
        ((Finset.univ : Finset {x : ℕ // x ∈ c}).image g) ∧
      p.target ⊆ q.target ∧
      ∀ x : {x : ℕ // x ∈ p.source},
        (q.equiv ⟨x.val, hs x.property⟩).val =
          (p.equiv x).val := by
  classical
  let C := {x : ℕ // x ∈ c}
  let d : Finset ℕ := (Finset.univ : Finset C).image g
  let q : FiniteStrongPartialIso M N :=
    { source := c
      target := d
      equiv := FiniteSpan.finiteImageEquiv g hg
      source_global := hc
      target_global := hGlobalG
      induced := by
        intro x y
        exact hIndG x y }
  have ht : p.target ⊆ q.target := by
    intro y hy
    let x : {x : ℕ // x ∈ p.source} :=
      p.equiv.symm ⟨y, hy⟩
    have hx : x.val ∈ c := hac x.property
    have hNumeric : g ⟨x.val, hx⟩ = y := by
      calc
        g ⟨x.val, hx⟩ = (p.equiv x).val := hBase x
        _ = y := by simp [x]
    exact Finset.mem_image.mpr
      ⟨⟨x.val, hx⟩, Finset.mem_univ _, hNumeric⟩
  refine ⟨q, hac, rfl, rfl, ht, ?_⟩
  intro x
  change g ⟨x.val, hac x.property⟩ = (p.equiv x).val
  exact hBase x

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
