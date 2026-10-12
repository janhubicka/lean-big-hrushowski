import BigHrushovski.InducedClosureDiagrams
import BigHrushovski.StrongConjugates

/-!
# Finite automorphism orbits and strong closures

A finite subset of the countable strong generic is intrinsically
strongly closed precisely when every element of it has a finite
orbit under the pointwise stabilizer of its generators.

More precisely, a vertex a lies in the finite strong closure of s
if and only if all images of a under induced automorphisms fixing s
pointwise are contained in a common finite set.

The forward implication uses the verified uniqueness of induced
copies of the finite strong-closure diagram over s. The converse
uses the verified ability to move every vertex outside the closure
beyond any prescribed finite forbidden set by an automorphism fixing s.

This is the precise automorphism-theoretic boundary of the manuscript's
assertion acl(s) = cl_s(s). The identification with *first-order*
algebraic closure still requires semantics for finite algebraic
formulas and the finite induced closure diagram.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A bijection of the countable generic which preserves and reflects
its graph relation. -/
def IsGenericAutomorphism (e : ℕ ≃ ℕ) : Prop :=
  ∀ x y : ℕ,
    genericTwoSparseGraph.adj x y ↔
      genericTwoSparseGraph.adj (e x) (e y)

/-- The pointwise stabilizer condition for a finite set of vertices. -/
def FixesGenericSet (e : ℕ ≃ ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, e x = x

/-- The orbit of a under automorphisms fixing s pointwise is finite:
all its elements lie in some finite set. This does not invoke
model-theoretic first-order algebraic closure. -/
def HasFiniteGenericOrbitOver (s : Finset ℕ) (a : ℕ) : Prop :=
  ∃ f : Finset ℕ,
    ∀ e : ℕ ≃ ℕ,
      IsGenericAutomorphism e →
      FixesGenericSet e s →
      e a ∈ f

/-- An induced automorphism fixing the generators maps the finite
strong closure onto itself (as a set, not pointwise). -/
theorem generic_automorphism_preserves_strongClosure
    (s : Finset ℕ) (e : ℕ ≃ ℕ)
    (hAut : IsGenericAutomorphism e)
    (hFix : FixesGenericSet e s) :
    (genericStrongClosure s).image e = genericStrongClosure s := by
  classical
  let c := genericStrongClosure s
  let f : {v : ℕ // v ∈ c} → ℕ := fun v => e v.val
  have hInj : Function.Injective f :=
    e.injective.comp Subtype.val_injective
  have hInduced : ∀ x y : {v : ℕ // v ∈ c},
      genericTwoSparseGraph.adj x.val y.val ↔
        genericTwoSparseGraph.adj (f x) (f y) :=
    fun x y => hAut x.val y.val
  have hFixed :
      ∀ x : {v : ℕ // v ∈ c}, x.val ∈ s → f x = x.val := by
    intro x hx
    exact hFix x.val hx
  have hCopy :=
    genericStrongClosure_induced_copy_image
      s f hInj hInduced hFixed
  have hSubtypeImage :
      (Finset.univ : Finset {v : ℕ // v ∈ c}).image f =
        c.image e := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, hx⟩
    · rintro ⟨x, hx, hzx⟩
      exact ⟨⟨x, hx⟩, hzx⟩
  calc
    (genericStrongClosure s).image e =
        (Finset.univ : Finset {v : ℕ // v ∈ c}).image f :=
      hSubtypeImage.symm
    _ = genericStrongClosure s := hCopy

/-- Every point of the finite strong closure has a finite orbit
under the pointwise stabilizer of its generators. -/
theorem genericStrongClosure_hasFiniteOrbit
    (s : Finset ℕ) (a : ℕ)
    (ha : a ∈ genericStrongClosure s) :
    HasFiniteGenericOrbitOver s a := by
  classical
  refine ⟨genericStrongClosure s, ?_⟩
  intro e hAut hFix
  have hImage :=
    generic_automorphism_preserves_strongClosure s e hAut hFix
  have hMember : e a ∈ (genericStrongClosure s).image e :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  rw [hImage] at hMember
  exact hMember

/-- Every vertex with finite stabilizer orbit must lie in the
finite strong closure of the generators. -/
theorem generic_hasFiniteOrbit_subset_strongClosure
    (s : Finset ℕ) (a : ℕ)
    (hOrbit : HasFiniteGenericOrbitOver s a) :
    a ∈ genericStrongClosure s := by
  obtain ⟨f, hf⟩ := hOrbit
  by_contra hOutside
  obtain ⟨e, hAut, hFix, hAvoid⟩ :=
    generic_outside_closure_infinite_orbit s a hOutside f
  exact hAvoid (hf e hAut hFix)

/-- Intrinsic finite strong closure coincides with the set of
vertices having finite automorphism orbit over the generators.
The model-theoretic acl equality is not asserted here. -/
theorem generic_hasFiniteOrbit_iff_strongClosure
    (s : Finset ℕ) (a : ℕ) :
    HasFiniteGenericOrbitOver s a ↔
      a ∈ genericStrongClosure s := by
  constructor
  · exact generic_hasFiniteOrbit_subset_strongClosure s a
  · exact genericStrongClosure_hasFiniteOrbit s a

end FiniteCatalogue
end BigHrushovski
