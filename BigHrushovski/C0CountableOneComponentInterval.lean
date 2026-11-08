import BigHrushovski.C0OneRemainingComponent
import BigHrushovski.C0CountableCanonicalStages

/-!
# Countable C₀: an intrinsic closed component interval is minimal strong

A countable graph with cofinal finite canonical C₀ presentations has
literal complete one-generated unary values on every finite stage.

Given two finite unary-closed sets Q⊆Z whose difference is the full
equality class of C-values of x, choose one finite canonical stage
containing Z. The intrinsic class is precisely one component of the
stage index, because equality of canonical values is equivalent to
equality of component indices. Restrict the ambient finite argument
to the stage subtype, and transport minimal strongness back to the
countable graph along the literal subtype inclusion.

This does not choose a global enumeration of components or any
special order inside a component. No countable functional Fraïssé
extension property is assumed.
-/

namespace BigHrushovski
namespace FiniteC0

/-- Any two finite complete-unary-closed subsets of a countable
canonical C₀ presentation that differ by exactly one entire intrinsic
unary-value class form a minimal strong step in the *original countable
graph*, not merely in one of its finite induced stages. -/
theorem canonicalStages_oneComponentInterval_minimal
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q Z : Finset ℕ) (hQZ : Q ⊆ Z)
    (hClosedQ : N.IsClosedUnderValues C Q)
    (hClosedZ : N.IsClosedUnderValues C Z)
    (x : ℕ)
    (hDiff : ∀ y : ℕ, y ∈ Z \ Q ↔ C y = C x) :
    N.toPredimension.IsMinimalStrongStep Q Z := by
  classical
  have hxDiff : x ∈ Z \ Q := (hDiff x).mpr rfl
  have hxZ : x ∈ Z := (Finset.mem_sdiff.mp hxDiff).1
  obtain ⟨n, hn⟩ := hCover Z
  let T := {v : ℕ // v ∈ stage n}
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  let Qt : Finset T :=
    (Finset.univ : Finset T).filter (fun v => v.val ∈ Q)
  let Zt : Finset T :=
    (Finset.univ : Finset T).filter (fun v => v.val ∈ Z)
  have hQStage : Q ⊆ stage n := hQZ.trans hn
  let xt : T := ⟨x, hn hxZ⟩
  obtain ⟨m, κ, hSteps, hValues⟩ := hStage n
  have hImageQ : Qt.image (Subtype.val : T → ℕ) = Q := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy
      exact huy ▸ (Finset.mem_filter.mp hu).2
    · intro hy
      exact Finset.mem_image.mpr
        ⟨⟨y, hQStage hy⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  have hImageZ : Zt.image (Subtype.val : T → ℕ) = Z := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy
      exact huy ▸ (Finset.mem_filter.mp hu).2
    · intro hy
      exact Finset.mem_image.mpr
        ⟨⟨y, hn hy⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  have hQtZt : Qt ⊆ Zt := by
    intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hQZ (Finset.mem_filter.mp hv).2⟩
  have hClosedQt :
      G.IsClosedUnderValues (canonicalValue G κ) Qt := by
    intro u hu v hv
    have huQ : u.val ∈ Q := (Finset.mem_filter.mp hu).2
    have hvC : v.val ∈ C u.val := by
      rw [hValues u]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hClosedQ u.val huQ hvC⟩
  have hClosedZt :
      G.IsClosedUnderValues (canonicalValue G κ) Zt := by
    intro u hu v hv
    have huZ : u.val ∈ Z := (Finset.mem_filter.mp hu).2
    have hvC : v.val ∈ C u.val := by
      rw [hValues u]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hClosedZ u.val huZ hvC⟩
  have hDiffT : Zt \ Qt = component κ (κ xt).val := by
    ext u
    constructor
    · intro hu
      have huZ : u.val ∈ Z :=
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
      have huNotQ : u.val ∉ Q := by
        intro huQ
        exact (Finset.mem_sdiff.mp hu).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ⟩)
      have huDiff : u.val ∈ Z \ Q :=
        Finset.mem_sdiff.mpr ⟨huZ, huNotQ⟩
      have huVal : C u.val = C x := (hDiff u.val).mp huDiff
      have hImgEq :
          (canonicalValue G κ u).image
              (Subtype.val : T → ℕ) =
            (canonicalValue G κ xt).image
              (Subtype.val : T → ℕ) := by
        calc
          (canonicalValue G κ u).image
                (Subtype.val : T → ℕ) = C u.val :=
              (hValues u).symm
          _ = C x := huVal
          _ = (canonicalValue G κ xt).image
                (Subtype.val : T → ℕ) := hValues xt
      have hValEq :
          canonicalValue G κ u = canonicalValue G κ xt :=
        Finset.image_injective
          (Subtype.val_injective : Function.Injective
            (Subtype.val : T → ℕ)) hImgEq
      have hIndex : κ u = κ xt :=
        (canonicalValue_eq_iff_index_eq G κ u xt).mp hValEq
      exact (mem_component_iff κ (κ xt).val u).mpr
        (congrArg Fin.val hIndex)
    · intro hu
      have hIndex : κ u = κ xt := Fin.ext
        ((mem_component_iff κ (κ xt).val u).mp hu)
      have hValEq :
          canonicalValue G κ u = canonicalValue G κ xt :=
        (canonicalValue_eq_iff_index_eq G κ u xt).mpr hIndex
      have hCeq : C u.val = C x := by
        calc
          C u.val = (canonicalValue G κ u).image
              (Subtype.val : T → ℕ) := hValues u
          _ = (canonicalValue G κ xt).image
              (Subtype.val : T → ℕ) := by rw [hValEq]
          _ = C x := (hValues xt).symm
      have huDiff : u.val ∈ Z \ Q := (hDiff u.val).mpr hCeq
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp huDiff).1⟩
      · intro huQt
        exact (Finset.mem_sdiff.mp huDiff).2
          (Finset.mem_filter.mp huQt).2
  have hFinite :
      G.toPredimension.IsMinimalStrongStep Qt Zt :=
    closed_one_component_interval_minimal
      G κ hSteps Qt Zt hQtZt hClosedQt hClosedZt xt hDiffT
  have hAdj : ∀ u v : T,
      G.adj u v ↔ N.adj u.val v.val := by
    intro u v
    rfl
  have hTransport :
      N.toPredimension.IsMinimalStrongStep
        (Qt.image (Subtype.val : T → ℕ))
        (Zt.image (Subtype.val : T → ℕ)) :=
    (G.minimalStrongStep_image_iff N
      (Subtype.val : T → ℕ)
      Subtype.val_injective hAdj Qt Zt hQtZt).mpr hFinite
  rw [hImageQ, hImageZ] at hTransport
  exact hTransport

end FiniteC0
end BigHrushovski
