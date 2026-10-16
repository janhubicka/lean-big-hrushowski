import BigHrushovski.CFExactOldFreshBoundary
import BigHrushovski.CFCountableResponse

/-!
# A complete one-block response over an arbitrary prescribed old source

A tagged C_F request r supplies its complete local graph on its
named support P and fresh ordered block B_r. Suppose S is a finite
old source, f:S→U an induced old embedding with d-closed image,
and the desired graph H on S ⊕ B_r is the free extension over P:
its old part is induced by f, its fresh-fresh graph agrees with
r's local code, and its old-fresh edges are exactly those from
that code on the literal support P (none outside P).

The tagged batch construction then gives an induced injection of
the *whole* desired graph H into the next finite level, not merely
an injection of its small support+block subgraph. Its finite image
is strictly d-closed in the entire simultaneous batch, and thus
globally d-closed in the countable birth-labelled graph.

The source vertices are fixed pointwise under the old inclusion.
There is no assumption that H already embeds into the generic.
This module still starts with a concrete actual request r whose
local code has the prescribed boundary and with the given old
embedding f; normalization of an arbitrary minimal extension
into such an r is a separate final bridge.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {S U : Type*}
variable [Fintype S] [DecidableEq S]
variable [Fintype U] [DecidableEq U]

/-- Insert an arbitrary old source by its prescribed old embedding,
and send each new ordinal to the exact tagged block of r. -/
def taggedCompleteMap
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (f : S → U) :
    Sum S (Fin r.code.1.val) →
      LevelCarrier G Allowed bound
  | Sum.inl s => Sum.inl (f s)
  | Sum.inr i => Sum.inr ⟨r, i⟩

/-- Neither old vertices nor fresh vertices are identified by
the complete tagged map, provided the old source map is injective. -/
theorem taggedCompleteMap_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (f : S → U) (hf : Function.Injective f) :
    Function.Injective (taggedCompleteMap G Allowed bound r f) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          apply congrArg Sum.inl
          apply hf
          exact Sum.inl.inj hxy
      | inr y =>
          cases hxy
  | inr x =>
      cases y with
      | inl y =>
          cases hxy
      | inr y =>
          have h : (⟨r, x⟩ : FreshCarrier G Allowed bound) =
              ⟨r, y⟩ := Sum.inr.inj hxy
          have hxy' : x = y := by
            cases h
            rfl
          exact congrArg Sum.inr hxy'

/-- The complete image is exactly the given old source together
with the chosen tagged fresh block. -/
theorem taggedCompleteMap_image
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (f : S → U) :
    ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image
      (taggedCompleteMap G Allowed bound r f)) =
      (((Finset.univ : Finset S).image f).image Sum.inl) ∪
        taggedBlock G Allowed bound r := by
  classical
  rw [← CFLocalCatalogue.old_union_fresh S r.code.1.val,
    Finset.image_union]
  congr 1
  · simp only [CFLocalCatalogue.oldVertices, Finset.image_image]
    rfl
  · simp only [CFLocalCatalogue.freshVertices, taggedBlock,
      Finset.image_image]
    rfl

/-- A free one-block extension of a complete old source is induced
in the actual tagged level. The boundary equivalence rules out
all extra edges to old vertices outside the named support. -/
theorem taggedCompleteMap_induced
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (f : S → U)
    (H : GraphOn (Sum S (Fin r.code.1.val)))
    (hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔ G.adj (f x) (f y))
    (hFresh : ∀ i j : Fin r.code.1.val,
      H.adj (Sum.inr i) (Sum.inr j) ↔
        r.code.2.graph.adj (Sum.inr i) (Sum.inr j))
    (hBoundary : ∀ x : S, ∀ i : Fin r.code.1.val,
      H.adj (Sum.inl x) (Sum.inr i) ↔
        ∃ q : SupportCarrier U r.support,
          q.val = f x ∧
          r.code.2.graph.adj (Sum.inl q) (Sum.inr i))
    (x y : Sum S (Fin r.code.1.val)) :
    H.adj x y ↔ (levelGraph G Allowed bound).adj
      (taggedCompleteMap G Allowed bound r f x)
      (taggedCompleteMap G Allowed bound r f y) := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact (hOld x y).trans
            (levelGraph_old_iff G Allowed bound (f x) (f y)).symm
      | inr i =>
          exact (hBoundary x i).trans
            (tagged_old_fresh_adj_iff G Allowed bound r (f x) i).symm
  | inr i =>
      cases y with
      | inl y =>
          have hSrc : H.adj (Sum.inr i) (Sum.inl y) ↔
              H.adj (Sum.inl y) (Sum.inr i) :=
            ⟨fun h => H.symm _ _ h,
              fun h => H.symm _ _ h⟩
          have hTarget :
              (levelGraph G Allowed bound).adj
                (Sum.inr ⟨r, i⟩) (Sum.inl (f y)) ↔
              (levelGraph G Allowed bound).adj
                (Sum.inl (f y)) (Sum.inr ⟨r, i⟩) :=
            ⟨fun h => (levelGraph G Allowed bound).symm _ _ h,
              fun h => (levelGraph G Allowed bound).symm _ _ h⟩
          exact hSrc.trans
            ((hBoundary y i).trans
              (tagged_old_fresh_adj_iff G Allowed bound r (f y) i).symm)
            |>.trans hTarget.symm
      | inr j =>
          have hLocal :=
            levelGraph_local_adj_iff G Allowed bound r
              (Sum.inr i) (Sum.inr j)
          exact (hFresh i j).trans hLocal.symm

/-- Full finite one-block response: the source+block graph is
induced, and its complete image remains strictly d-closed
after the *entire* finite request batch has been attached. -/
theorem taggedCompleteMap_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (f : S → U) (hf : Function.Injective f)
    (hSourceClosed : G.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ)
    (hSupport : r.support ⊆
      ((Finset.univ : Finset S).image f)) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image
        (taggedCompleteMap G Allowed bound r f))
      Finset.univ := by
  classical
  rw [taggedCompleteMap_image]
  exact taggedResponse_dClosed_full G Allowed bound
    ((Finset.univ : Finset S).image f)
    hSourceClosed r hSupport

end CFStageCatalogue

namespace CFCoherentTower

open CFStageCatalogue

/-- One complete tagged block realizes a requested finite graph
over the prescribed old map, with a globally strictly d-closed
image in the actual countable birth graph. Every old source
vertex keeps its birth-labelled identity. -/
theorem completeOneBlock_global
    {S : Type*} [Fintype S] [DecidableEq S]
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (f : S → (stage F K n).carrier) (hf : Function.Injective f)
    (r : Requests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card))
    (H : GraphOn (Sum S (Fin r.code.1.val)))
    (hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage F K n).graph.adj (f x) (f y))
    (hFresh : ∀ i j : Fin r.code.1.val,
      H.adj (Sum.inr i) (Sum.inr j) ↔
        r.code.2.graph.adj (Sum.inr i) (Sum.inr j))
    (hBoundary : ∀ x : S, ∀ i : Fin r.code.1.val,
      H.adj (Sum.inl x) (Sum.inr i) ↔
        ∃ q : SupportCarrier (stage F K n).carrier r.support,
          q.val = f x ∧
          r.code.2.graph.adj (Sum.inl q) (Sum.inr i))
    (hSourceClosed : (stage F K n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ)
    (hSupport : r.support ⊆
      ((Finset.univ : Finset S).image f)) :
    ∃ g : Sum S (Fin r.code.1.val) → Vertex F K,
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) = toVertex F K n (f x)) ∧
      (∀ x y : Sum S (Fin r.code.1.val),
        H.adj x y ↔ (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image g) := by
  classical
  let G := (stage F K n).graph
  let allowed : AllowedLocal (stage F K n).carrier :=
    GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  let fStage : Sum S (Fin r.code.1.val) →
      (stage F K (n + 1)).carrier :=
    taggedCompleteMap G allowed bound r f
  let g : Sum S (Fin r.code.1.val) → Vertex F K :=
    fun x => toVertex F K (n + 1) (fStage x)
  have hInj : Function.Injective g :=
    (toVertex_injective F K (n + 1)).comp
      (taggedCompleteMap_injective G allowed bound r f hf)
  have hAdjStage : ∀ x y : Sum S (Fin r.code.1.val),
      H.adj x y ↔
        (stage F K (n + 1)).graph.adj (fStage x) (fStage y) := by
    intro x y
    exact taggedCompleteMap_induced G allowed bound r f H
      hOld hFresh hBoundary x y
  have hAdjGlobal : ∀ x y : Sum S (Fin r.code.1.val),
      H.adj x y ↔ (countableGraph F K).adj (g x) (g y) := by
    intro x y
    exact (hAdjStage x y).trans
      (countableGraph_stage_induced F K (n + 1)
        (fStage x) (fStage y)).symm
  have hFiniteClosed :
      (stage F K (n + 1)).graph.toPredimension.IsDClosed
        ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image
          fStage) Finset.univ :=
    taggedCompleteMap_dClosed_full G allowed bound r f hf
      hSourceClosed hSupport
  have hGlobalClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image g) := by
    have hImage :
        ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image g) =
        (((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image
          fStage).image (toVertex F K (n + 1))) := by
      simp only [Finset.image_image]
      rfl
    rw [hImage]
    exact finiteClosedPart_global F K (n + 1)
      ((Finset.univ : Finset (Sum S (Fin r.code.1.val))).image fStage)
      hFiniteClosed
  refine ⟨g, hInj, ?_, hAdjGlobal, hGlobalClosed⟩
  intro x
  exact toVertex_old F K n (f x)

end CFCoherentTower
end BigHrushovski
