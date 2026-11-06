import Mathlib

/-!
# The closure-splicing calculation for the C₀ Ellentuck space

The finite-set-theoretic part of the manuscript's proof of A.3(2) does not
depend on the predimension or on the particular enumeration of C₀.  It
depends only on the full one-generated closure and its transitivity.

This module formalizes that common calculation, including preservation of
the whole depth prefix and elimination of all unwanted components from
stem-compatible closed copies.  It intentionally does *not* claim the
tail-extension property of the spliced set, which is the remaining
structural ingredient in A.3(2) and requires the C₀ functional generic.
-/

namespace BigHrushovski.Ellentuck

universe u

variable {Vertex : Type u}
variable (Γ : Vertex → Set Vertex)

/-- A set is closed under the complete one-generated closures. -/
def IsUnaryClosed (S : Set Vertex) : Prop :=
  ∀ ⦃v⦄, v ∈ S → Γ v ⊆ S

/-- Retain X, and temporarily allow vertices whose closure uses the
protected remainder D of the ambient approximation. -/
def forcedBody (Y X D : Set Vertex) : Set Vertex :=
  X ∪ {v | v ∈ Y ∧ ∃ d, d ∈ Γ v ∧ d ∈ D}

/-- Take the largest unary-closed part of the forced body inside Y. -/
def splicedCore (Y X D : Set Vertex) : Set Vertex :=
  {v | v ∈ Y ∧ Γ v ⊆ forcedBody Γ Y X D}

/-- The two-step splicing construction is unary-closed whenever Y is
unary-closed and Γ is transitive.  The intermediate forced body need not
itself be closed. -/
theorem splicedCore_closed
    {Y X D : Set Vertex}
    (hY : IsUnaryClosed Γ Y)
    (htrans : ∀ v w, w ∈ Γ v → Γ w ⊆ Γ v) :
    IsUnaryClosed Γ (splicedCore Γ Y X D) := by
  intro v hv w hw
  change w ∈ Y ∧ Γ w ⊆ forcedBody Γ Y X D
  constructor
  · exact hY hv.1 hw
  · exact (htrans v w hw).trans hv.2

/-- The original smaller closed copy X is retained in the spliced core. -/
theorem subset_splicedCore_of_closed
    {Y X D : Set Vertex}
    (hX : IsUnaryClosed Γ X) (hXY : X ⊆ Y) :
    X ⊆ splicedCore Γ Y X D := by
  intro v hv
  refine ⟨hXY hv, ?_⟩
  intro w hw
  exact Or.inl (hX hv hw)

/-- The full ambient depth prefix C is retained. It is enough that
C is closed and every vertex in C belongs either to X or to D=C\\a.
There is no need to require a special order on C at this stage. -/
theorem prefix_subset_splicedCore
    {Y X D C : Set Vertex}
    (hrefl : ∀ v, v ∈ Γ v)
    (hC : IsUnaryClosed Γ C)
    (hCY : C ⊆ Y)
    (hcover : C ⊆ X ∪ D) :
    C ⊆ splicedCore Γ Y X D := by
  intro v hv
  refine ⟨hCY hv, ?_⟩
  intro w hw
  have hwC : w ∈ C := hC hv hw
  rcases hcover hwC with hwX | hwD
  · exact Or.inl hwX
  · exact Or.inr ⟨hCY hwC, w, hrefl w, hwD⟩

/-- A closed copy Z which avoids the unwanted part D cannot use any
of the extra vertices introduced in the splicing. This is the
stem-preserving part of A.3(2), prior to building the ambient copy
inside the spliced set. -/
theorem closed_subset_splicedCore_subset_X
    {Y X D Z : Set Vertex}
    (hrefl : ∀ v, v ∈ Γ v)
    (hZ : IsUnaryClosed Γ Z)
    (hZV : Z ⊆ splicedCore Γ Y X D)
    (hZD : Disjoint Z D) :
    Z ⊆ X := by
  intro v hv
  have hvV := hZV hv
  have hvW : v ∈ forcedBody Γ Y X D := hvV.2 (hrefl v)
  rcases hvW with hvX | hvD
  · exact hvX
  · rcases hvD with ⟨_, d, hdΓ, hdD⟩
    exact False.elim ((Set.disjoint_left.mp hZD) (hZ hv hdΓ) hdD)

end BigHrushovski.Ellentuck
