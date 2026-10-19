import BigHrushovski.CFSelectedClosedSubbatch
import BigHrushovski.CFCountableResponse

/-!
# Globally d-closed finite sets in the actual birth-block presentation

A vertex of the countable C_F birth graph remembers a unique level,
the actual request tag at that level, and its fresh ordinal.

Call a finite set block-support-closed when meeting a fresh block
forces the *entire* block and its literally named support into the
set. This is exactly closure under the auxiliary set-valued unary
operation b(v)=P_B ∪ B of the manuscript, without constructing any
quotient or independently renumbering vertices.

We show that every stage cut of such a set is d-closed in its actual
finite tagged stage, using the verified selected-closed-subbatch
lemma. The countable strict d-closed stage chain then promotes this
to global strict d-closedness of the original finite set.

No growth bound, generalized inverse, or class-level free amalgamation
hypothesis is needed here: these are structural facts of the
already constructed tagged graph. The full root-recovery identity
H(R(v))=C(v) remains a separate assertion.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The literal request type for new vertices born at level n. -/
abbrev BirthRequest (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :=
  Requests (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card)

/-- Finite cut in the original stage carrier; it is *not*
an arbitrarily chosen copy of the induced source graph. -/
noncomputable def stageCut (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ) :
    Finset (stage F K n).carrier := by
  classical
  exact (Finset.univ : Finset (stage F K n).carrier).filter
    (fun v => toVertex F K n v ∈ s)

theorem mem_stageCut_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (v : (stage F K n).carrier) :
    v ∈ stageCut F K s n ↔ toVertex F K n v ∈ s := by
  classical
  simp [stageCut]

/-- The exact auxiliary b-closure predicate: all fresh ordinals
of a request and every vertex of its old support must be selected
as soon as any fresh ordinal of that request is selected. -/
def IsBirthBlockClosed (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Prop :=
  ∀ (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val),
    (⟨n, (⟨r, i⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ s →
    (∀ j : Fin r.code.1.val,
      (⟨n, (⟨r, j⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ s) ∧
    (∀ u ∈ r.support, toVertex F K n u ∈ s)

/-- Actual complete fresh blocks met by s at stage n. -/
noncomputable def selectedRequests (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ) :
    Finset (BirthRequest F K n) := by
  classical
  exact (Finset.univ : Finset (BirthRequest F K n)).filter
    (fun r => ∃ i : Fin r.code.1.val,
      (⟨n, (⟨r, i⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ s)

theorem mem_selectedRequests_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (r : BirthRequest F K n) :
    r ∈ selectedRequests F K s n ↔
      ∃ i : Fin r.code.1.val,
        (⟨n, (⟨r, i⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ s := by
  classical
  simp [selectedRequests]

/-- Exactly the selected requests contribute fresh vertices to
the successor stage cut; the old part is the previous cut. -/
theorem stageCut_succ_eq_selected
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ) :
    stageCut F K s (n + 1) =
      ((stageCut F K s n).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n+1)).carrier)) ∪
      (selectedRequests F K s n).biUnion
        (taggedBlock (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)) := by
  classical
  let G := (stage F K n).graph
  let Allowed := GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  ext v
  cases v with
  | inl u =>
      constructor
      · intro hv
        apply Finset.mem_union.mpr
        apply Or.inl
        apply Finset.mem_image.mpr
        refine ⟨u, ?_, rfl⟩
        apply (mem_stageCut_iff F K s n u).mpr
        have hs' := (mem_stageCut_iff F K s (n+1) (Sum.inl u)).mp hv
        simpa only [toVertex_old] using hs'
      · intro hv
        rcases Finset.mem_union.mp hv with hOld | hFresh
        · obtain ⟨u', hu', huEq⟩ := Finset.mem_image.mp hOld
          have hu : u' = u := Sum.inl.inj huEq
          subst u'
          apply (mem_stageCut_iff F K s (n+1) (Sum.inl u)).mpr
          simpa only [toVertex_old] using
            (mem_stageCut_iff F K s n u).mp hu'
        · obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hFresh
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
          cases hi
  | inr fresh =>
      obtain ⟨r, i⟩ := fresh
      constructor
      · intro hv
        apply Finset.mem_union.mpr
        apply Or.inr
        apply Finset.mem_biUnion.mpr
        refine ⟨r, ?_, ?_⟩
        · apply (mem_selectedRequests_iff F K s n r).mpr
          refine ⟨i, ?_⟩
          have h := (mem_stageCut_iff F K s (n+1)
            (Sum.inr ⟨r,i⟩)).mp hv
          simpa only [toVertex_new] using h
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · intro hv
        rcases Finset.mem_union.mp hv with hOld | hFresh
        · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hOld
          cases hu
        · obtain ⟨q, hq, hblock⟩ := Finset.mem_biUnion.mp hFresh
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hblock
          have hqEq : q = r :=
            congrArg Sigma.fst (Sum.inr.inj hj)
          subst q
          obtain ⟨k, hk⟩ :=
            (mem_selectedRequests_iff F K s n r).mp hq
          have hBlock := (hs n r k hk).1 i
          apply (mem_stageCut_iff F K s (n+1)
            (Sum.inr ⟨r,i⟩)).mpr
          simpa only [toVertex_new] using hBlock

/-- The old component of the selected successor cut consists
exactly of the old-stage cut and is strictly d-closed there. -/
theorem stageCut_succ_old_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hCut : (stage F K n).graph.toPredimension.IsDClosed
      (stageCut F K s n) Finset.univ) :
    (stage F K (n+1)).graph.toPredimension.IsDClosed
      ((stageCut F K s n).image Sum.inl)
      (taggedOldDomain (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)) := by
  classical
  have hAdj : ∀ u v : (stage F K n).carrier,
      (stage F K n).graph.adj u v ↔
        (stage F K (n+1)).graph.adj (Sum.inl u) (Sum.inl v) := by
    intro u v
    exact (stage_succ_induced F K n u v).symm
  exact (((stage F K n).graph).dClosed_image_iff
    (stage F K (n+1)).graph Sum.inl
    (Sum.inl_injective) hAdj
    (stageCut F K s n) Finset.univ (Finset.subset_univ _)).mpr hCut

/-- The literal supports of selected requests belong to
the complete old-stage cut, not merely an isomorphic copy. -/
theorem selectedRequests_supports_subset_old
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ) :
    ∀ r ∈ selectedRequests F K s n,
      taggedSupport (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r ⊆
      (stageCut F K s n).image Sum.inl := by
  intro r hr v hv
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
  obtain ⟨i, hi⟩ := (mem_selectedRequests_iff F K s n r).mp hr
  have hsU : toVertex F K n u ∈ s :=
    (hs n r i hi).2 u hu
  exact Finset.mem_image.mpr
    ⟨u, (mem_stageCut_iff F K s n u).mpr hsU, huv⟩

/-- Every stage cut is strictly d-closed in its actual
finite tagged graph. The proof follows the selected blocks
at a level, with no second induction over the requests. -/
theorem stageCut_dClosed_of_birthBlockClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ) :
    (stage F K n).graph.toPredimension.IsDClosed
      (stageCut F K s n) Finset.univ := by
  induction n with
  | zero =>
      have hEmpty : stageCut F K s 0 = ∅ := by
        ext v
        exact Fin.elim0 v
      rw [hEmpty]
      simpa using (stage F K 0).graph.toPredimension.dclosed_refl
        (∅ : Finset (stage F K 0).carrier)
  | succ n ih =>
      have hOld := stageCut_succ_old_dClosed F K s n ih
      have hSupports := selectedRequests_supports_subset_old F K s hs n
      have hFull := taggedSupportClosedSubbatch_dClosed_full
        (stage F K n).graph (GrowthAllowedLocal F)
        (fun P => K P.card)
        (selectedRequests F K s n)
        ((stageCut F K s n).image Sum.inl)
        hOld hSupports
      rw [stageCut_succ_eq_selected F K s hs n]
      exact hFull

/-- A finite subset closed under the auxiliary birth-block
operation b(v)=P_B∪B is globally strictly d-closed in the
actual countable tagged C_F graph. -/
theorem birthBlockClosed_global_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) :
    (countableGraph F K).toPredimension.IsGloballyDClosed s := by
  classical
  obtain ⟨n, hn⟩ := finiteSet_covered F K s
  have hImage :
      (stageCut F K s n).image (toVertex F K n) = s := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      rw [← huv]
      exact (mem_stageCut_iff F K s n u).mp hu
    · intro hv
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (hn hv)
      apply Finset.mem_image.mpr
      refine ⟨u, ?_, hu⟩
      exact (mem_stageCut_iff F K s n u).mpr (hu ▸ hv)
  have hFinite : (stage F K n).graph.toPredimension.IsDClosed
      (stageCut F K s n) Finset.univ :=
    stageCut_dClosed_of_birthBlockClosed F K s hs n
  rw [← hImage]
  exact finiteClosedPart_global F K n (stageCut F K s n) hFinite

end CFCoherentTower
