import BigHrushovski.C0FunctionalFairGeneric

/-!
# Track A: complete named unary values of a finite closed base

Let A be an arbitrary finite subset of the actual countable C₀
functional limit, closed under the whole set-valued unary function C.
Its induced finite function on the literal named carrier A is simply
the original complete value, with each vertex represented as a subtype.

When A is included in a larger finite canonical stage S, the literal
injection A → S transports this *complete* named function exactly
into the canonical value of each base point in S. Thus the common
base function used by the finite two-sided amalgamation theorem can
be constructed from A rather than postulated separately.

This is the finite compatibility step in extending stage genericity
to arbitrary finite closed bases. No model-theoretic homogeneity
statement is made here.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The literal named unary function on a finite closed carrier:
all of C(a), with its vertices represented as elements of s. -/
noncomputable def namedClosedBaseValue
    (C : ℕ → Finset ℕ) (s : Finset ℕ)
    (a : {v : ℕ // v ∈ s}) : Finset {v : ℕ // v ∈ s} := by
  classical
  exact (Finset.univ : Finset {v : ℕ // v ∈ s}).filter
    (fun b => b.val ∈ C a.val)

/-- Closure of s is exactly the hypothesis ensuring that the
whole original value C(a) is recovered from the named base, without
discarding any vertex in a later stage. -/
theorem namedClosedBaseValue_image
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (s : Finset ℕ) (hClosed : N.IsClosedUnderValues C s)
    (a : {v : ℕ // v ∈ s}) :
    (namedClosedBaseValue C s a).image
      (Subtype.val : {v : ℕ // v ∈ s} → ℕ) = C a.val := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hb).2
  · intro hx
    have hxs : x ∈ s := hClosed a.val a.property hx
    exact Finset.mem_image.mpr
      ⟨⟨x, hxs⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

/-- The literal base inclusion into an enclosing finite stage. -/
def closedBaseStageInclusion
    (s t : Finset ℕ) (hst : s ⊆ t) :
    {v : ℕ // v ∈ s} → {v : ℕ // v ∈ t} :=
  fun a => ⟨a.val, hst a.property⟩

theorem closedBaseStageInclusion_injective
    (s t : Finset ℕ) (hst : s ⊆ t) :
    Function.Injective (closedBaseStageInclusion s t hst) := by
  intro a b h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- The literal induced base graph embeds into the enclosing
canonical stage, reflecting every edge and nonedge. -/
theorem closedBaseStageInclusion_induced
    (N : GraphOn ℕ) (s t : Finset ℕ)
    (hst : s ⊆ t)
    (a b : {v : ℕ // v ∈ s}) :
    (N.pullback (Subtype.val : {v : ℕ // v ∈ s} → ℕ)).adj a b ↔
      (N.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ)).adj
        (closedBaseStageInclusion s t hst a)
        (closedBaseStageInclusion s t hst b) := by
  rfl

/-- If a canonical index on a finite stage has the exact ambient
C-values, the complete canonical value of every base point is the
image of the *constructed* named base function. This is the exact
`F(p)` compatibility input to the tagged two-sided functional
amalgamation theorem.

The result uses full unary-value agreement on the enclosing stage
and C-closedness of the base; no common chronological index on
the base is chosen. -/
theorem canonicalStage_complete_namedBase_values
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (t s : Finset ℕ) (hst : s ⊆ t)
    (hClosed : N.IsClosedUnderValues C s)
    {m : ℕ} (κ : {v : ℕ // v ∈ t} → Fin m)
    (hValues : ∀ a : {v : ℕ // v ∈ t},
      C a.val =
        (canonicalValue
          (N.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
          κ a).image
            (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
    (a : {v : ℕ // v ∈ s}) :
    canonicalValue
        (N.pullback (Subtype.val : {v : ℕ // v ∈ t} → ℕ))
        κ (closedBaseStageInclusion s t hst a) =
      (namedClosedBaseValue C s a).image
        (closedBaseStageInclusion s t hst) := by
  classical
  let S := {v : ℕ // v ∈ s}
  let T := {v : ℕ // v ∈ t}
  let e : S → T := closedBaseStageInclusion s t hst
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  apply Finset.image_injective
    (Subtype.val_injective : Function.Injective
      (Subtype.val : T → ℕ))
  have hCompose :
      (Subtype.val : T → ℕ) ∘ e =
        (Subtype.val : S → ℕ) := by
    funext x
    rfl
  calc
    (canonicalValue G κ (e a)).image (Subtype.val : T → ℕ) =
        C a.val := by
          exact (hValues (e a)).symm
    _ = (namedClosedBaseValue C s a).image
        (Subtype.val : S → ℕ) :=
          (namedClosedBaseValue_image N C s hClosed a).symm
    _ = ((namedClosedBaseValue C s a).image e).image
        (Subtype.val : T → ℕ) := by
          rw [Finset.image_image, hCompose]

end FiniteC0
end BigHrushovski
