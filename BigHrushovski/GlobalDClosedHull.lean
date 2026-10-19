import BigHrushovski.MinimalRootForcing
import BigHrushovski.CFCountableDClosedChain
import BigHrushovski.CFDClosedHull

/-!
# Least globally d-closed hulls under a strict countable exhaustion

Let d be a finite submodular predimension on a possibly infinite
vertex type, and let e be a countable chain of *finite*, strictly
d-closed stages covering the carrier.

For any finite set S choose a stage U_n containing S. The least
finite strict d-closed hull of S inside U_n is globally strictly
d-closed, because U_n is globally d-closed. Its leastness does
not depend on the chosen stage: every competing globally d-closed
finite set T may be cut down to T∩U_n; the finite-cut restriction
lemma says this intersection is d-closed in U_n.

Consequently every finite S has a canonical least globally
d-closed finite hull. We prove extensivity, monotonicity,
idempotence, and independence of a chosen finite stage.

This is reusable beyond C_F, and gives the graph-theoretic
meaning of the partial operation H on finite block-root sets.
It is not yet the identity H(R(v))=C(v).
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- A finite generator has a least finite globally strictly
d-closed hull whenever there is a countable finite d-closed
exhaustion. No class membership or Fraïssé genericity is used. -/
theorem exists_least_globalDClosed_hull
    (d : Predimension V) (e : DClosedChain d) (s : Finset V) :
    ∃ h : Finset V,
      s ⊆ h ∧ d.IsGloballyDClosed h ∧
      ∀ t : Finset V,
        s ⊆ t → d.IsGloballyDClosed t → h ⊆ t := by
  classical
  obtain ⟨n, hs⟩ := e.contains_finite s
  let h := d.dClosedHull s (e.stage n)
  have hClosed : d.IsDClosed h (e.stage n) :=
    d.dClosedHull_dclosed s (e.stage n)
  have hGlobal : d.IsGloballyDClosed h :=
    d.globallyDClosed_of_dClosed_in_global hClosed (e.stage_global n)
  have hS : s ⊆ h :=
    d.subset_dClosedHull hs
  refine ⟨h, hS, hGlobal, ?_⟩
  intro t hst hGlob
  have hTClosed : d.IsDClosed t (t ∪ e.stage n) :=
    hGlob.restrict Finset.subset_union_left
  have hTcap : d.IsDClosed (t ∩ e.stage n) (e.stage n) :=
    d.dclosed_inter_restrict hTClosed Finset.subset_union_right
  have hScap : s ⊆ t ∩ e.stage n := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hst hv, hs hv⟩
  have hSub : h ⊆ t ∩ e.stage n :=
    d.dClosedHull_least hScap hTcap
  exact hSub.trans Finset.inter_subset_left

/-- Canonical finite hull, characterized by global strict
d-closedness and universal leastness. -/
noncomputable def globalDClosedHull
    (d : Predimension V) (e : DClosedChain d) (s : Finset V) : Finset V :=
  Classical.choose (d.exists_least_globalDClosed_hull e s)

theorem subset_globalDClosedHull
    (d : Predimension V) (e : DClosedChain d) (s : Finset V) :
    s ⊆ d.globalDClosedHull e s :=
  (Classical.choose_spec (d.exists_least_globalDClosed_hull e s)).1

theorem globalDClosedHull_global
    (d : Predimension V) (e : DClosedChain d) (s : Finset V) :
    d.IsGloballyDClosed (d.globalDClosedHull e s) :=
  (Classical.choose_spec (d.exists_least_globalDClosed_hull e s)).2.1

theorem globalDClosedHull_least
    (d : Predimension V) (e : DClosedChain d)
    {s t : Finset V}
    (hst : s ⊆ t) (ht : d.IsGloballyDClosed t) :
    d.globalDClosedHull e s ⊆ t :=
  (Classical.choose_spec (d.exists_least_globalDClosed_hull e s)).2.2
    t hst ht

/-- Different finite globally closed containers yield the same
global hull; the result is not tied to the chosen stage in the
exhaustion. -/
theorem globalDClosedHull_eq_finiteStageHull
    (d : Predimension V) (e : DClosedChain d)
    (s : Finset V) (n : ℕ) (hs : s ⊆ e.stage n) :
    d.globalDClosedHull e s = d.dClosedHull s (e.stage n) := by
  have hFinite : d.IsDClosed
      (d.dClosedHull s (e.stage n)) (e.stage n) :=
    d.dClosedHull_dclosed s (e.stage n)
  have hGlobal : d.IsGloballyDClosed
      (d.dClosedHull s (e.stage n)) :=
    d.globallyDClosed_of_dClosed_in_global hFinite (e.stage_global n)
  have hSub : d.globalDClosedHull e s ⊆
      d.dClosedHull s (e.stage n) :=
    d.globalDClosedHull_least e (d.subset_dClosedHull hs) hGlobal
  have hStage : d.globalDClosedHull e s ⊆ e.stage n :=
    d.globalDClosedHull_least e hs (e.stage_global n)
  have hRel : d.IsDClosed (d.globalDClosedHull e s) (e.stage n) :=
    (d.globalDClosedHull_global e s).restrict hStage
  have hOther : d.dClosedHull s (e.stage n) ⊆
      d.globalDClosedHull e s :=
    d.dClosedHull_least (d.subset_globalDClosedHull e s) hRel
  exact le_antisymm hSub hOther

theorem globalDClosedHull_mono
    (d : Predimension V) (e : DClosedChain d)
    {s t : Finset V} (hst : s ⊆ t) :
    d.globalDClosedHull e s ⊆ d.globalDClosedHull e t :=
  d.globalDClosedHull_least e
    (hst.trans (d.subset_globalDClosedHull e t))
    (d.globalDClosedHull_global e t)

theorem globalDClosedHull_idempotent
    (d : Predimension V) (e : DClosedChain d) (s : Finset V) :
    d.globalDClosedHull e (d.globalDClosedHull e s) =
      d.globalDClosedHull e s := by
  apply le_antisymm
  · exact d.globalDClosedHull_least e Finset.Subset.rfl
      (d.globalDClosedHull_global e s)
  · exact d.subset_globalDClosedHull e (d.globalDClosedHull e s)

end Predimension

namespace CFCoherentTower

/-- Graph-theoretic d-closure of a finite set of birth vertices.
Its finiteness and global leastness are unconditional structural
consequences of the concrete strict stage chain. -/
noncomputable def birthDClosedHull
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Finset (Vertex F K) :=
  (countableGraph F K).toPredimension.globalDClosedHull
    (birthDClosedChain F K) s

theorem birthDClosedHull_global
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      (birthDClosedHull F K s) :=
  (countableGraph F K).toPredimension.globalDClosedHull_global
    (birthDClosedChain F K) s

theorem birthDClosedHull_eq_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n : ℕ) (hs : s ⊆ stageImage F K n) :
    birthDClosedHull F K s =
      (countableGraph F K).toPredimension.dClosedHull
        s (stageImage F K n) :=
  (countableGraph F K).toPredimension.globalDClosedHull_eq_finiteStageHull
    (birthDClosedChain F K) s n hs

end CFCoherentTower
end BigHrushovski
