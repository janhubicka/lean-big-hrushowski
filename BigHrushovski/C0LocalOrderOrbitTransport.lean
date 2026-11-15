import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.C0FairVertexRankIso

/-!
# Track A: transports of finite ordered one-generated closure types

A chosen ordered representative of a finite one-generated functional
C₀ type does not determine one automorphism-invariant linear order on
the labelled vertices of every occurrence. It determines one *orbit*
of orders under its automorphism group fixing the already ordered
lower part.

We isolate the exact finite isomorphism argument. If e₁ and e₂ are
complete-functional isomorphisms from the same occurrence to the same
representative, then e₁ followed by the inverse of e₂ is a complete-
functional automorphism of the occurrence. If the transports agree
on the ordered lower part, this automorphism fixes it pointwise. It
also aligns the two transported linear orders.

Finally a complete local linear order has a trivial stabilizer:
an automorphism preserving an injective rank on all vertices is the
identity. This is why the number of order transports in an orbit is
the size of the corresponding automorphism group.

This module proves the finite *transport* interface, not the
subsequent choice of one orbit for each local type along the countable
fair chronology. No claim about a big Ramsey theorem is made.
-/

namespace BigHrushovski
namespace FiniteC0

variable {A R : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype R] [DecidableEq R]

/-- Changing between two isomorphisms from an occurrence to the
same finite representative induces an automorphism of its carrier. -/
noncomputable def localRepresentativeChange
    (e₁ e₂ : A ≃ R) : A ≃ A :=
  e₁.trans e₂.symm

theorem localRepresentativeChange_spec
    (e₁ e₂ : A ≃ R) (x : A) :
    e₂ (localRepresentativeChange e₁ e₂ x) = e₁ x := by
  simp [localRepresentativeChange]

/-- If both identifications agree on the lower part, their change
of coordinates fixes each lower vertex literally, not merely setwise. -/
theorem localRepresentativeChange_fixesLower
    (e₁ e₂ : A ≃ R) (P : Finset A)
    (hAgree : ∀ x ∈ P, e₁ x = e₂ x) :
    ∀ x ∈ P, localRepresentativeChange e₁ e₂ x = x := by
  intro x hx
  apply e₂.injective
  rw [localRepresentativeChange_spec]
  exact hAgree x hx

/-- Two transports of an injective numeric ordering rank have
identical comparisons after the finite change-of-coordinates map. -/
theorem localRepresentativeChange_alignsOrder
    (e₁ e₂ : A ≃ R) (rank : R → ℕ)
    (x y : A) :
    (rank (e₁ x) < rank (e₁ y)) ↔
      (rank (e₂ (localRepresentativeChange e₁ e₂ x)) <
        rank (e₂ (localRepresentativeChange e₁ e₂ y))) := by
  rw [localRepresentativeChange_spec, localRepresentativeChange_spec]

/-- If both identifications are induced graph isomorphisms and
preserve complete unary values, their change of coordinates is
a *full functional automorphism* of the occurrence. -/
theorem localRepresentativeChange_fullFunctional
    (G : GraphOn A) (H : GraphOn R)
    (CA : A → Finset A) (CR : R → Finset R)
    (e₁ e₂ : A ≃ R)
    (hAdj₁ : ∀ x y : A, G.adj x y ↔ H.adj (e₁ x) (e₁ y))
    (hAdj₂ : ∀ x y : A, G.adj x y ↔ H.adj (e₂ x) (e₂ y))
    (hValue₁ : ∀ x : A, CR (e₁ x) = (CA x).image e₁)
    (hValue₂ : ∀ x : A, CR (e₂ x) = (CA x).image e₂) :
    (∀ x y : A,
      G.adj x y ↔
        G.adj (localRepresentativeChange e₁ e₂ x)
          (localRepresentativeChange e₁ e₂ y)) ∧
    (∀ x : A,
      CA (localRepresentativeChange e₁ e₂ x) =
        (CA x).image (localRepresentativeChange e₁ e₂)) := by
  classical
  let g : A ≃ A := localRepresentativeChange e₁ e₂
  have hEval (x : A) : e₂ (g x) = e₁ x :=
    localRepresentativeChange_spec e₁ e₂ x
  have hComp : e₂ ∘ g = e₁ := by
    funext x
    exact hEval x
  constructor
  · intro x y
    calc
      G.adj x y ↔ H.adj (e₁ x) (e₁ y) :=
        hAdj₁ x y
      _ ↔ H.adj (e₂ (g x)) (e₂ (g y)) := by
        rw [hEval x, hEval y]
      _ ↔ G.adj (g x) (g y) :=
        (hAdj₂ (g x) (g y)).symm
  · intro x
    apply Finset.image_injective e₂.injective
    calc
      (CA (g x)).image e₂ = CR (e₂ (g x)) :=
        (hValue₂ (g x)).symm
      _ = CR (e₁ x) := by rw [hEval x]
      _ = (CA x).image e₁ := hValue₁ x
      _ = ((CA x).image g).image e₂ := by
        simpa only [Finset.image_image, hComp]

/-- Two full-functional transports of the same ordered representative
are aligned by a full-functional automorphism fixing the lower part.
In particular the induced orders are isomorphic *over* that lower
part, although they need not coincide on labelled new vertices. -/
theorem localRepresentative_transports_sameOrbit
    (G : GraphOn A) (H : GraphOn R)
    (CA : A → Finset A) (CR : R → Finset R)
    (P : Finset A) (rank : R → ℕ)
    (e₁ e₂ : A ≃ R)
    (hAgree : ∀ x ∈ P, e₁ x = e₂ x)
    (hAdj₁ : ∀ x y : A, G.adj x y ↔ H.adj (e₁ x) (e₁ y))
    (hAdj₂ : ∀ x y : A, G.adj x y ↔ H.adj (e₂ x) (e₂ y))
    (hValue₁ : ∀ x : A, CR (e₁ x) = (CA x).image e₁)
    (hValue₂ : ∀ x : A, CR (e₂ x) = (CA x).image e₂) :
    ∃ g : A ≃ A,
      (∀ x ∈ P, g x = x) ∧
      (∀ x y : A, G.adj x y ↔ G.adj (g x) (g y)) ∧
      (∀ x : A, CA (g x) = (CA x).image g) ∧
      (∀ x y : A,
        (rank (e₁ x) < rank (e₁ y)) ↔
          (rank (e₂ (g x)) < rank (e₂ (g y)))) := by
  refine ⟨localRepresentativeChange e₁ e₂,
    localRepresentativeChange_fixesLower e₁ e₂ P hAgree, ?_, ?_, ?_⟩
  · exact (localRepresentativeChange_fullFunctional
      G H CA CR e₁ e₂ hAdj₁ hAdj₂ hValue₁ hValue₂).1
  · exact (localRepresentativeChange_fullFunctional
      G H CA CR e₁ e₂ hAdj₁ hAdj₂ hValue₁ hValue₂).2
  · exact localRepresentativeChange_alignsOrder e₁ e₂ rank

/-- An automorphism preserving an injective rank on **all** vertices
is the identity. Applied to a linear order on the finite new
component, this is the freeness behind local order-orbit counts. -/
theorem localRepresentative_orderStabilizer_trivial
    (e : A ≃ R) (rank : R → ℕ)
    (hRank : Function.Injective rank)
    (g : A ≃ A)
    (hPreserve : ∀ x : A, rank (e (g x)) = rank (e x)) :
    g = Equiv.refl A := by
  ext x
  apply e.injective
  exact hRank (hPreserve x)

end FiniteC0
end BigHrushovski
