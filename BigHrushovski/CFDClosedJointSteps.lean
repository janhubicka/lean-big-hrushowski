import BigHrushovski.CFDClosedBackAndForthCore
import BigHrushovski.CFGrowthClass
import BigHrushovski.FiniteImageEquiv
import BigHrushovski.StrongJointExtension

/-!
# Strict d-closed joint steps from complete finite responses

This is the finite constructive part of the countable C_F recognition
argument. It is independent of the canonical birth-labelled tower:
the latter must later be shown to satisfy the input response predicate.

A finite strong container is NOT sufficient. Every chosen container,
every prescribed old image and every new image are globally **strictly
d-closed**. Source and target graphs satisfy the SAME exact growth
inequality; arbitrary 2-sparse graphs are not substituted for C_F.

The generic coherent-union lemma is imported from
CFDClosedBackAndForthCore. This file constructs its strict joint steps,
first going forth across a source vertex and then back across a target
vertex. All given values are fixed, and graph inducedness is an iff.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- Every finite set has a globally strictly d-closed finite
container. This is stronger than the usual strong-cover property. -/
def HasFiniteDClosedCovers (M : GraphOn ℕ) : Prop :=
  ∀ a : Finset ℕ, ∃ c : Finset ℕ,
    a ⊆ c ∧ M.toPredimension.IsGloballyDClosed c

/-- Global C_F membership on the actual countable graph, tested
against every finite subset. -/
def HasGrowthInequality (F : ℕ → ℝ) (M : GraphOn ℕ) : Prop :=
  ∀ s : Finset ℕ, F s.card ≤ (M.predim s : ℝ)

/-- Literal finite d-closed response property, including all
old labels and nonedges. The source is the finite interval a ≤d b
of an arbitrary graph on ℕ, and need only satisfy the growth
bound on b. The target N receives a complete induced copy. -/
def HasFiniteDClosedIntervalResponses
    (F : ℕ → ℝ) (N : GraphOn ℕ) : Prop :=
  ∀ (M : GraphOn ℕ) (a b : Finset ℕ),
    M.IsGrowthSparse F b →
    (hab : M.toPredimension.IsDClosed a b) →
    ∀ (e : {x : ℕ // x ∈ a} → ℕ),
      Function.Injective e →
      (∀ x y : {x : ℕ // x ∈ a},
        M.adj x.val y.val ↔ N.adj (e x) (e y)) →
      N.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {x : ℕ // x ∈ a}).image e) →
      ∃ g : {x : ℕ // x ∈ b} → ℕ,
        Function.Injective g ∧
        (∀ x : {x : ℕ // x ∈ a},
          g ⟨x.val, hab.1 x.property⟩ = e x) ∧
        (∀ x y : {x : ℕ // x ∈ b},
          M.adj x.val y.val ↔ N.adj (g x) (g y)) ∧
        N.toPredimension.IsGloballyDClosed
          ((Finset.univ : Finset {x : ℕ // x ∈ b}).image g)

namespace PartialIso

variable {M N : GraphOn ℕ}

/-- Reverse a strictly d-closed partial graph isomorphism;
the inverse remains strictly d-closed on both sides. -/
noncomputable def symm (p : PartialIso M N) : PartialIso N M where
  source := p.target
  target := p.source
  equiv := p.equiv.symm
  source_global := p.target_global
  target_global := p.source_global
  induced := by
    intro x y
    simpa using (p.induced (p.equiv.symm x) (p.equiv.symm y)).symm

private theorem symm_symm (p : PartialIso M N) :
    p.symm.symm = p := by
  cases p
  simp [symm]

/-- The conversion to the weak-strong union type commutes
with reversing a finite partial isomorphism. -/
theorem toStrong_symm (p : PartialIso M N) :
    p.symm.toStrong = p.toStrong.symm := by
  cases p
  rfl

/-- Exact extension is preserved on reversing the finite maps.
This reuses the already certified C_0 inverse extension theorem;
no duplicate inverse-map calculation is needed. -/
theorem Extends.inverse {p q : PartialIso M N}
    (hpq : Extends p q) : Extends p.symm q.symm := by
  have h := FiniteCatalogue.FiniteStrongPartialIso.Extends.inverse hpq
  simpa only [Extends, toStrong_symm] using h

/-- The current source map can be extended to a finite globally
strictly d-closed container c containing any prescribed vertex.
This is the strict analogue of C_0's strong forth step; finite
target growth and the complete old-fresh graph are explicit. -/
theorem exists_extending_forth
    (F : ℕ → ℝ) (M N : GraphOn ℕ)
    (hGrowthM : HasGrowthInequality F M)
    (hCoverM : HasFiniteDClosedCovers M)
    (hRespN : HasFiniteDClosedIntervalResponses F N)
    (p : PartialIso M N) (v : ℕ) :
    ∃ q : PartialIso M N,
      Extends p q ∧ v ∈ q.source := by
  classical
  obtain ⟨c, hContains, hcClosed⟩ :=
    hCoverM (insert v p.source)
  have hac : p.source ⊆ c := by
    intro x hx
    exact hContains (Finset.mem_insert_of_mem hx)
  have hv : v ∈ c :=
    hContains (Finset.mem_insert_self v p.source)
  have hAC : M.toPredimension.IsDClosed p.source c :=
    Predimension.IsGloballyDClosed.restrict M.toPredimension p.source_global hac
  have hGrowthC : M.IsGrowthSparse F c := by
    intro s _
    exact hGrowthM s
  let e : {x : ℕ // x ∈ p.source} → ℕ :=
    fun x => (p.equiv x).val
  have heInj : Function.Injective e := by
    intro x y hxy
    exact p.equiv.injective (Subtype.ext hxy)
  have heAdj : ∀ x y : {x : ℕ // x ∈ p.source},
      M.adj x.val y.val ↔ N.adj (e x) (e y) :=
    p.induced
  have heImage :
      ((Finset.univ : Finset {x : ℕ // x ∈ p.source}).image e) =
      p.target := by
    exact p.toStrong.image_equiv_eq_target
  have heClosed : N.toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset {x : ℕ // x ∈ p.source}).image e) := by
    rw [heImage]
    exact p.target_global
  obtain ⟨g, hgInj, hgOld, hgAdj, hgClosed⟩ :=
    hRespN M p.source c hGrowthC hAC
      e heInj heAdj heClosed
  let image : Finset ℕ :=
    (Finset.univ : Finset {x : ℕ // x ∈ c}).image g
  let q : PartialIso M N :=
    { source := c
      target := image
      equiv := FiniteSpan.finiteImageEquiv g hgInj
      source_global := hcClosed
      target_global := hgClosed
      induced := by
        intro x y
        exact hgAdj x y }
  have hpq : Extends p q := by
    refine ⟨hac, ?_, ?_⟩
    · intro y hy
      let x : {x : ℕ // x ∈ p.source} :=
        p.equiv.symm ⟨y, hy⟩
      have hNumeric : g ⟨x.val, hac x.property⟩ = y := by
        calc
          g ⟨x.val, hac x.property⟩ = e x := hgOld x
          _ = y := by simp [e, x]
      exact Finset.mem_image.mpr
        ⟨⟨x.val, hac x.property⟩, Finset.mem_univ _, hNumeric⟩
    · intro x
      change g ⟨x.val, hac x.property⟩ = (p.equiv x).val
      exact hgOld x
  exact ⟨q, hpq, hv⟩

/-- The strict back step is the strict forth step of the inverse map.
The old target images and all their values remain unchanged. -/
theorem exists_extending_back
    (F : ℕ → ℝ) (M N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality F N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hRespM : HasFiniteDClosedIntervalResponses F M)
    (p : PartialIso M N) (v : ℕ) :
    ∃ q : PartialIso M N,
      Extends p q ∧ v ∈ q.target := by
  obtain ⟨q, hpq, hv⟩ :=
    exists_extending_forth F N M hGrowthN hCoverN
      hRespM p.symm v
  refine ⟨q.symm, ?_, hv⟩
  have h := Extends.inverse hpq
  rw [symm_symm p] at h
  exact h

/-- The two strict finite responses yield the exact joint-step
hypothesis required by the common coherent-union theorem. -/
theorem hasJointSteps_of_finiteDClosedResponses
    (F : ℕ → ℝ) (M N : GraphOn ℕ)
    (hGrowthM : HasGrowthInequality F M)
    (hGrowthN : HasGrowthInequality F N)
    (hCoverM : HasFiniteDClosedCovers M)
    (hCoverN : HasFiniteDClosedCovers N)
    (hRespM : HasFiniteDClosedIntervalResponses F M)
    (hRespN : HasFiniteDClosedIntervalResponses F N) :
    HasJointSteps M N := by
  intro k p
  obtain ⟨q, hpq, hkSource⟩ :=
    exists_extending_forth F M N hGrowthM hCoverM hRespN p k
  obtain ⟨r, hqr, hkTarget⟩ :=
    exists_extending_back F M N hGrowthN hCoverN hRespM q k
  refine ⟨r,
    (FiniteCatalogue.FiniteStrongPartialIso.Extends.trans hpq hqr),
    ?_, hkTarget⟩
  exact hqr.1 hkSource

end PartialIso

/-- Countable strong-limit recognition for the finite strict C_F
extension property. This is the previously missing conditional
strict d-closed back-and-forth theorem on natural-number carriers.

The published exact C_F assumptions and transfer from the actual
birth-labelled graph to a natural-number presentation are still
needed to specialize it to M_F. -/
theorem exists_induced_equiv_of_finiteDClosedResponses
    (F : ℕ → ℝ) (M N : GraphOn ℕ)
    (hGrowthM : HasGrowthInequality F M)
    (hGrowthN : HasGrowthInequality F N)
    (hCoverM : HasFiniteDClosedCovers M)
    (hCoverN : HasFiniteDClosedCovers N)
    (hRespM : HasFiniteDClosedIntervalResponses F M)
    (hRespN : HasFiniteDClosedIntervalResponses F N)
    (hEmptyM : M.toPredimension.IsGloballyDClosed ∅)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ e : ℕ ≃ ℕ,
      ∀ x y : ℕ, M.adj x y ↔ N.adj (e x) (e y) := by
  exact PartialIso.exists_induced_equiv_of_joint_steps
    M N hEmptyM hEmptyN
    (PartialIso.hasJointSteps_of_finiteDClosedResponses
      F M N hGrowthM hGrowthN hCoverM hCoverN hRespM hRespN)

end CFDClosedBackAndForth
end BigHrushovski
