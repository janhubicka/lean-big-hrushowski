import BigHrushovski.CFStageCutBirthImage
import BigHrushovski.CFStageBirthOrderCoherence

/-!
# Canonical finite C_F source-cut identification across arbitrary gaps

A finite birth-labelled source need not meet every level of the
countable C_F tower. If no source vertex is born in [n,m),
the literal stage-n and stage-m cuts have precisely the same
birth-labelled vertices. We make their canonical correspondence
an explicit equivalence of the two *actual finite cut subtypes*.

This avoids repeated casts between dependent finite-stage carriers.
Its two maps preserve the literal birth labels, the complete
induced graph (including nonedges), and the inherited stage order.

There is no renumbering, no choice of an abstract graph copy,
and no extension of the prescribed finite level assignment to
a strictly increasing self-map of all natural numbers.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every old cut vertex has a representative at the later cut
with the SAME actual countable birth label whenever there are
no represented source levels in the intervening interval. -/
theorem stageCutGap_exists
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    ∃ v : SupportCarrier (stage F K m).carrier (stageCut F K s m),
      toVertex F K m v.val = toVertex F K n u.val := by
  classical
  have hCut := stageCut_birthImage_eq_of_noLevelsBetween
    F K s n m hnm hGap
  have hu : toVertex F K n u.val ∈
      (stageCut F K s m).image (toVertex F K m) := by
    rw [← hCut]
    exact Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩
  obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp hu
  exact ⟨⟨v, hv⟩, huv⟩

/-- The canonical map of actual source cuts across a gap;
its vertex representative is selected by the exact birth label. -/
noncomputable def stageCutGapMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i) :
    SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      SupportCarrier (stage F K m).carrier (stageCut F K s m) :=
  fun u => Classical.choose (stageCutGap_exists F K s n m hnm hGap u)

/-- The map is not just an abstract isomorphism: the actual
countable birth label of every selected source vertex is fixed. -/
theorem stageCutGapMap_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    toVertex F K m (stageCutGapMap F K s n m hnm hGap u).val =
      toVertex F K n u.val :=
  Classical.choose_spec (stageCutGap_exists F K s n m hnm hGap u)

/-- Uniqueness of a stage representative of each birth-labelled
vertex makes the canonical source-gap map injective. -/
theorem stageCutGapMap_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i) :
    Function.Injective (stageCutGapMap F K s n m hnm hGap) := by
  intro u v huv
  apply Subtype.ext
  apply toVertex_injective F K n
  calc
    toVertex F K n u.val =
        toVertex F K m (stageCutGapMap F K s n m hnm hGap u).val :=
      (stageCutGapMap_birth F K s n m hnm hGap u).symm
    _ = toVertex F K m (stageCutGapMap F K s n m hnm hGap v).val := by
      rw [huv]
    _ = toVertex F K n v.val :=
      stageCutGapMap_birth F K s n m hnm hGap v

/-- All vertices in the later literal cut arise from the earlier
cut; the source has no new birth levels in the gap. -/
theorem stageCutGapMap_surjective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i) :
    Function.Surjective (stageCutGapMap F K s n m hnm hGap) := by
  classical
  intro v
  have hCut := stageCut_birthImage_eq_of_noLevelsBetween
    F K s n m hnm hGap
  have hv : toVertex F K m v.val ∈
      (stageCut F K s n).image (toVertex F K n) := by
    rw [hCut]
    exact Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply toVertex_injective F K m
  calc
    toVertex F K m (stageCutGapMap F K s n m hnm hGap ⟨u, hu⟩).val =
      toVertex F K n u :=
        stageCutGapMap_birth F K s n m hnm hGap ⟨u, hu⟩
    _ = toVertex F K m v.val := huv

/-- The genuine source-cut correspondence, preserving the
countable birth label of every literal vertex. -/
noncomputable def stageCutGapEquiv
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i) :
    SupportCarrier (stage F K n).carrier (stageCut F K s n) ≃
      SupportCarrier (stage F K m).carrier (stageCut F K s m) :=
  Equiv.ofBijective (stageCutGapMap F K s n m hnm hGap)
    ⟨stageCutGapMap_injective F K s n m hnm hGap,
     stageCutGapMap_surjective F K s n m hnm hGap⟩

/-- The cut equivalence acts by the identity on actual birth
labels; it does not choose a fresh copy of the source graph. -/
theorem stageCutGapEquiv_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    toVertex F K m (stageCutGapEquiv F K s n m hnm hGap u).val =
      toVertex F K n u.val :=
  stageCutGapMap_birth F K s n m hnm hGap u

/-- The canonical gap equivalence preserves and reflects all
old graph edges and nonedges on the literal finite source cut. -/
theorem stageCutGapEquiv_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u v : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (stage F K n).graph.adj u.val v.val ↔
      (stage F K m).graph.adj
        (stageCutGapEquiv F K s n m hnm hGap u).val
        (stageCutGapEquiv F K s n m hnm hGap v).val := by
  calc
    (stage F K n).graph.adj u.val v.val ↔
      (countableGraph F K).adj
        (toVertex F K n u.val) (toVertex F K n v.val) :=
          (countableGraph_stage_induced F K n u.val v.val).symm
    _ ↔ (countableGraph F K).adj
      (toVertex F K m (stageCutGapEquiv F K s n m hnm hGap u).val)
      (toVertex F K m (stageCutGapEquiv F K s n m hnm hGap v).val) := by
        rw [stageCutGapEquiv_birth, stageCutGapEquiv_birth]
    _ ↔ _ := countableGraph_stage_induced F K m _ _

/-- It also preserves and reflects the inherited finite stage
order, because both orders are restrictions of the same
canonical countable birth order. -/
theorem stageCutGapEquiv_stageOrder_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u v : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    stageLt F K n u.val v.val ↔
      stageLt F K m
        (stageCutGapEquiv F K s n m hnm hGap u).val
        (stageCutGapEquiv F K s n m hnm hGap v).val := by
  calc
    stageLt F K n u.val v.val ↔
      canonicalBirthLt F K (toVertex F K n u.val)
        (toVertex F K n v.val) :=
          stageLt_iff_canonicalBirthLt F K n u.val v.val
    _ ↔ canonicalBirthLt F K
      (toVertex F K m (stageCutGapEquiv F K s n m hnm hGap u).val)
      (toVertex F K m (stageCutGapEquiv F K s n m hnm hGap v).val) := by
        rw [stageCutGapEquiv_birth, stageCutGapEquiv_birth]
    _ ↔ _ := (stageLt_iff_canonicalBirthLt F K m _ _).symm

end CFCoherentTower
end BigHrushovski
