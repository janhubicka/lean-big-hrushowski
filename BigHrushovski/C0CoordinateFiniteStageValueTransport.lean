import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.C0CoordinateRawClosedOverlap

/-!
# Transport of finite canonical C₀ stage and complete-value witnesses

The two-sided finite C₀ amalgamation theorem produces a finite
component indexing whose consecutive stages may be EMPTY or minimal
strong. The initial literal raw-code witnesses instead use nonempty
minimal-strong steps. The two formats must not be conflated.

We keep the broader finite presentation, with all complete canonical
unary values specified explicitly. It transports along a bijection
preserving and reflecting every graph edge, including nonedges,
together with all complete named unary values.

This lemma is a preparation for transporting a tagged free amalgam
to a literal finite closed union in the raw coordinate host.
It does not itself assert the converse finite-age theorem,
two-sparseness, an ordered catalogue, W or the return embedding.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- A finite canonical C₀ component presentation with complete
specified unary values, allowing empty component stages. This is
the stage/value witness used in the existing finite functional
amalgamation theorem; it is not restricted to the stricter raw
code generator presentation. -/
def HasCanonicalC0StageValues
    (G : GraphOn U) (C : U → Finset U) : Prop :=
  ∃ (n : ℕ) (κ : U → Fin n),
    (∀ k : ℕ, k < n →
      FiniteC0.oldStage κ k = FiniteC0.oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k) (FiniteC0.oldStage κ (k+1))) ∧
    (∀ u : U, FiniteC0.canonicalValue G κ u = C u)

/-- Transport a complete finite canonical C₀ presentation across an
induced graph equivalence, with all complete C-values transported
as exact finite sets. In particular negative graph and unary
incidences are reflected and no empty component stage is removed
without justification. -/
theorem hasCanonicalC0StageValues_equiv
    (G : GraphOn U) (H : GraphOn V)
    (C : U → Finset U) (D : V → Finset V)
    (e : U ≃ V)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (e x) (e y))
    (hValues : ∀ x : U, (C x).image e = D (e x))
    (hG : HasCanonicalC0StageValues G C) :
    HasCanonicalC0StageValues H D := by
  classical
  obtain ⟨n, κ, hSteps, hC⟩ := hG
  refine ⟨n, FiniteC0.relabelIndex κ e,
    FiniteC0.minimalSteps_relabel G H e hAdj κ hSteps, ?_⟩
  intro v
  let u : U := e.symm v
  have huv : e u = v := e.apply_symm_apply v
  rw [← huv]
  calc
    FiniteC0.canonicalValue H
        (FiniteC0.relabelIndex κ e) (e u) =
      (FiniteC0.canonicalValue G κ u).image e :=
        FiniteC0.canonicalValue_relabel G H e hAdj κ u
    _ = (C u).image e := by rw [hC u]
    _ = D (e u) := hValues u

/-- A finite canonical witness also transports backwards under the
same complete graph and unary equivalence. This is useful when a
literal union is identified with an already presented free amalgam:
neither direction requires a new canonical enumeration. -/
theorem hasCanonicalC0StageValues_equiv_iff
    (G : GraphOn U) (H : GraphOn V)
    (C : U → Finset U) (D : V → Finset V)
    (e : U ≃ V)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (e x) (e y))
    (hValues : ∀ x : U, (C x).image e = D (e x)) :
    HasCanonicalC0StageValues G C ↔
      HasCanonicalC0StageValues H D := by
  constructor
  · exact hasCanonicalC0StageValues_equiv
      G H C D e hAdj hValues
  · intro hH
    have hAdjBack : ∀ x y : V,
        H.adj x y ↔ G.adj (e.symm x) (e.symm y) := by
      intro x y
      simpa only [e.apply_symm_apply] using
        (hAdj (e.symm x) (e.symm y)).symm
    have hValuesBack : ∀ x : V,
        (D x).image e.symm = C (e.symm x) := by
      intro x
      have h := hValues (e.symm x)
      rw [e.apply_symm_apply] at h
      rw [← h]
      simp only [Finset.image_image]
      have hEq : (e.symm ∘ e) = id := by
        funext y
        exact e.symm_apply_apply y
      rw [hEq, Finset.image_id]
    exact hasCanonicalC0StageValues_equiv
      H G D C e.symm hAdjBack hValuesBack hH

end FiniteUnaryCoordinates
end BigHrushovski
