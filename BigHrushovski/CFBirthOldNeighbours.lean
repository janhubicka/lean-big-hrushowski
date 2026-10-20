import BigHrushovski.CFBirthSupportRecovery
import BigHrushovski.CFExactOldFreshBoundary
import BigHrushovski.CFSupportPersistence

/-!
# Exact old neighbours of C_F tagged birth blocks

No vertex of the preceding finite birth stage U_n outside the
literal old support of a newly born request r has an edge to
that request's tagged fresh block. This is first a statement
about the actual simultaneous level graph and then about its
induced copy in the countable birth graph.

Consequently the entire old-neighbour set of that block in U_n
is the same as its old-neighbour set within its support.
The equality persists for every intermediate old subset A with
P_r ⊆ A ⊆ U_n.

These are the no-cross identities needed in the final intrinsic
support computation inside the generated closure C(v), whose
earlier vertices all lie in the old stage.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- An old vertex of stage n adjacent in the countable graph to
a fresh birth vertex of request r lies in r's literal support. -/
theorem birthOldAdjacent_forces_support
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    {v w : Vertex F K}
    (hv : v ∈ stageImage F K n)
    (hw : w ∈ birthBlock F K n r)
    (hAdj : (countableGraph F K).adj v w) :
    v ∈ birthSupport F K n r := by
  classical
  let G := (stage F K n).graph
  let Allowed : AllowedLocal (stage F K n).carrier :=
    GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hv
  obtain ⟨z, hz, hzW⟩ := Finset.mem_image.mp hw
  obtain ⟨i, _, hiZ⟩ := Finset.mem_image.mp hz
  have hvOld : toVertex F K (n + 1) (Sum.inl u) = v :=
    (toVertex_old F K n u).trans hu
  have hwNew :
      toVertex F K (n + 1) (Sum.inr ⟨r, i⟩) = w := by
    calc
      toVertex F K (n + 1) (Sum.inr ⟨r,i⟩) =
          toVertex F K (n + 1) z := by rw [hiZ]
      _ = w := hzW
  have hStage :
      (stage F K (n + 1)).graph.adj
        (Sum.inl u) (Sum.inr ⟨r,i⟩) := by
    apply (countableGraph_stage_induced F K (n + 1)
      (Sum.inl u) (Sum.inr ⟨r,i⟩)).mp
    rw [hvOld, hwNew]
    exact hAdj
  obtain ⟨q, hqu, _⟩ :=
    (tagged_old_fresh_adj_iff G Allowed bound r u i).mp hStage
  have huP : u ∈ r.support := by
    rw [← hqu]
    exact q.property
  apply Finset.mem_image.mpr
  refine ⟨Sum.inl u, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨u, huP, rfl⟩
  · exact hvOld

/-- Old neighbours of a fresh block inside the full previous
stage are exactly the neighbours in the literal support.
There are no additional edges in the countable limit. -/
theorem birthOldNeighbours_eq_supportNeighbours
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    (countableGraph F K).oldNeighbourSet
      (stageImage F K n) (birthBlock F K n r) =
        birthSupportNeighbours F K n r := by
  let G := countableGraph F K
  exact G.oldNeighbourSet_eq_of_backNeighbours
    (birthSupport F K n r) (stageImage F K n)
    (birthBlock F K n r)
    (by
      intro v hv
      exact (mem_stageImage_iff_birth_lt F K n v).mpr
        (birthSupport_birth_lt F K n r hv))
    (by
      intro u hu v hv huv
      exact birthOldAdjacent_forces_support F K n r hv hu
        (G.symm _ _ huv))

/-- The same old-neighbour computation holds inside *any*
earlier induced vertex subset A containing the named support.
This is the precise form needed for C(v) minus its top block. -/
theorem birthOldNeighbours_eq_within_old
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (A : Finset (Vertex F K))
    (hP : birthSupport F K n r ⊆ A)
    (hA : A ⊆ stageImage F K n) :
    (countableGraph F K).oldNeighbourSet
      A (birthBlock F K n r) =
        birthSupportNeighbours F K n r := by
  let G := countableGraph F K
  exact G.oldNeighbourSet_eq_of_backNeighbours
    (birthSupport F K n r) A
    (birthBlock F K n r) hP
    (by
      intro u hu v hv huv
      exact birthOldAdjacent_forces_support F K n r (hA hv) hu
        (G.symm _ _ huv))

end CFCoherentTower
end BigHrushovski
