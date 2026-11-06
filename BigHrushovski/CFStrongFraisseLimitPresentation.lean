import BigHrushovski.CFFraisseThreeData
import BigHrushovski.CFDClosedChain
import BigHrushovski.CFCountableRelabelling

/-!
# The actual finite strong-limit characterization on an arbitrary carrier

The manuscript characterizes M_F as the countably infinite
Fraisse limit of (C_F, ≤_d): all of its finite subgraphs belong to
the growth class; it is a union of finite d-closed subgraphs; and
each finite d-closed extension is realized over a prescribed strong
embedding. These are the natural model-theoretic conditions,
without a fixed numbering of the actual vertices.

We show that this characterization implies the already
kernel-checked three-property countable strict genericity criterion.
In particular, finite global d-closed covers are a consequence of
the covering d-closed chain, not an extra hypothesis about M_F.

No isomorphism with the canonical birth graph is a field of this
interface, and the proof of the countable carrier transport
preserves and reflects edges, all old values and strict closure.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

variable {V : Type*} [DecidableEq V]

/-- The strong Fraisse extension property on the *original*
vertex set V, without choosing a numbering of its vertices.
Every finite growth-class interval A ≤_d B and every induced
globally strictly d-closed copy of A admits an induced globally
strictly d-closed copy of B over the same literal values. -/
def HasFiniteDClosedResponsesOn
    (F : ℕ → ℝ) (G : GraphOn V) : Prop :=
  ∀ (M : GraphOn ℕ) (a b : Finset ℕ),
    M.IsGrowthSparse F b →
    (hab : M.toPredimension.IsDClosed a b) →
    ∀ (f : {x : ℕ // x ∈ a} → V),
      Function.Injective f →
      (∀ x y : {x : ℕ // x ∈ a},
        M.adj x.val y.val ↔ G.adj (f x) (f y)) →
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {x : ℕ // x ∈ a}).image f) →
      ∃ g : {x : ℕ // x ∈ b} → V,
        Function.Injective g ∧
        (∀ x : {x : ℕ // x ∈ a},
          g ⟨x.val, hab.1 x.property⟩ = f x) ∧
        (∀ x y : {x : ℕ // x ∈ b},
          M.adj x.val y.val ↔ G.adj (g x) (g y)) ∧
        G.toPredimension.IsGloballyDClosed
          ((Finset.univ : Finset {x : ℕ // x ∈ b}).image g)

/-- The original-carrier finite extension property passes
unchanged to any numbering by ℕ. Unlike arbitrary induced
injections, a carrier equivalence preserves global strict
d-closedness against every finite ambient extension. -/
theorem HasFiniteDClosedResponsesOn.pullback
    (F : ℕ → ℝ) (G : GraphOn V)
    (ι : ℕ ≃ V)
    (hResp : HasFiniteDClosedResponsesOn F G) :
    HasFiniteDClosedIntervalResponses F (G.pullback ι) := by
  classical
  intro M a b hGrowth hab f hfInj hfAdj hfClosed
  let fV : {x : ℕ // x ∈ a} → V := fun x => ι (f x)
  have hfVInj : Function.Injective fV :=
    ι.injective.comp hfInj
  have hfVAdj : ∀ x y : {x : ℕ // x ∈ a},
      M.adj x.val y.val ↔ G.adj (fV x) (fV y) := by
    intro x y
    exact hfAdj x y
  have hOldImage :
      ((Finset.univ : Finset {x : ℕ // x ∈ a}).image fV) =
      (((Finset.univ : Finset {x : ℕ // x ∈ a}).image f).image ι) := by
    rw [Finset.image_image]
    rfl
  have hfVClosed :
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {x : ℕ // x ∈ a}).image fV) := by
    rw [hOldImage]
    exact (G.globallyDClosed_pullback_iff ι
      ((Finset.univ : Finset {x : ℕ // x ∈ a}).image f)).mp hfClosed
  obtain ⟨gV, hgVInj, hgVOld, hgVAdj, hgVClosed⟩ :=
    hResp M a b hGrowth hab fV hfVInj hfVAdj hfVClosed
  let g : {x : ℕ // x ∈ b} → ℕ :=
    fun x => ι.symm (gV x)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact ι.symm.injective.comp hgVInj
  · intro x
    change ι.symm (gV ⟨x.val, hab.1 x.property⟩) = f x
    rw [hgVOld x]
    exact ι.symm_apply_apply (f x)
  · intro x y
    change M.adj x.val y.val ↔
      G.adj (ι (ι.symm (gV x))) (ι (ι.symm (gV y)))
    simpa only [ι.apply_symm_apply] using hgVAdj x y
  · apply (G.globallyDClosed_pullback_iff ι
        ((Finset.univ : Finset {x : ℕ // x ∈ b}).image g)).2
    have hImage :
        (((Finset.univ : Finset {x : ℕ // x ∈ b}).image g).image ι) =
        ((Finset.univ : Finset {x : ℕ // x ∈ b}).image gV) := by
      simp [g, Finset.image_image, Function.comp_def]
    rw [hImage]
    exact hgVClosed

/-- A strong Fraisse-limit presentation in the actual language
of graphs, with the manuscript's natural input data:
countably infinite enumeration, full finite age, an increasing
covering chain of finite d-closed substructures, and the
prescribed finite strong extension property. -/
structure StrongFraisseLimitPresentation
    (F : ℕ → ℝ) (G : GraphOn V) where
  enumerate : ℕ ≃ V
  age : ∀ s : Finset V, F s.card ≤ (G.predim s : ℝ)
  chain : Predimension.DClosedChain G.toPredimension
  finite_extensions : HasFiniteDClosedResponsesOn F G

/-- Every presented countable strong Fraisse limit has the
three finite recognition properties, now derived rather
than separately postulated. The finite globally d-closed
covers come from the defining covering strong chain. -/
theorem StrongFraisseLimitPresentation.toPresentedFraisseData
    (F : ℕ → ℝ) (G : GraphOn V)
    (h : StrongFraisseLimitPresentation F G) :
    PresentedFraisseData F G := by
  classical
  have hCover : ∀ s : Finset V,
      ∃ c : Finset V,
        s ⊆ c ∧ G.toPredimension.IsGloballyDClosed c := by
    intro s
    obtain ⟨n, hn⟩ := h.chain.contains_finite s
    exact ⟨h.chain.stage n, hn, h.chain.stage_global n⟩
  exact {
    enumerate := h.enumerate
    finite_data := {
      growth := G.finiteGrowth_pullback h.enumerate F h.age
      finite_closed_covers :=
        G.finiteDClosedCover_pullback h.enumerate hCover
      finite_extensions :=
        HasFiniteDClosedResponsesOn.pullback F G
          h.enumerate h.finite_extensions
    }
  }

/-- The canonical C_F birth graph is isomorphic to a countable
strong Fraisse limit on its *given* carrier, with its finite
age, chain and extension properties explicitly stated.
The birth-construction hypothesis of a request at every level
is kept separate in this real-domain interface. -/
theorem realBirth_iso_strongFraisseLimit
    (F : ℝ → ℝ) (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : CFCoherentTower.HasFiniteClassDClosedFreeJoins
      (CFGrowthNumerics.cardinalGrowth F))
    (hRequests : ∀ n : ℕ,
      Nonempty (CFStageCatalogue.StageRequest
        (CFCoherentTower.stage
          (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) n).graph
        (CFStageCatalogue.GrowthAllowedLocal
          (CFGrowthNumerics.cardinalGrowth F))
        (fun P =>
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) P.card)))
    (hEmptyClass : HasClassDClosedEmpty (CFGrowthNumerics.cardinalGrowth F))
    (G : GraphOn V)
    (hG : StrongFraisseLimitPresentation
      (CFGrowthNumerics.cardinalGrowth F) G) :
    ∃ φ : CFCoherentTower.RealBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : CFCoherentTower.RealBirthVertex F hMono hUnbounded,
        (CFCoherentTower.realCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  exact CFCoherentTower.realBirth_iso_presentedFraisseData
    F hZero hMono hUnbounded hFree hRequests G
    (hG.toPresentedFraisseData
      (CFGrowthNumerics.cardinalGrowth F) G)
    hEmptyClass

end CFDClosedBackAndForth
end BigHrushovski
