import BigHrushovski.GlobalDClosedHull
import BigHrushovski.CFBirthGeneratedClosure
import BigHrushovski.CFTaggedBlockCertificates

/-!
# Minimal C_F blocks and their first vertices on the literal birth carrier

The countable birth graph consists of tagged finite local requests.
Each request r at level n has a literal old support P_r and a finite
fresh block B_r. This module transports their finite minimal strict
d-closed extension to the countable graph, preserving the actual
vertex names. It also identifies the first ordinal of each block.

The next root-recovery argument will invoke finite root forcing on
these actual image sets. No enumeration of the whole graph is added,
and the complete functional equation H(R(v))=C(v) is not asserted here.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The actual finite old support of one birth-level request. -/
noncomputable def birthSupport
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) : Finset (Vertex F K) := by
  classical
  exact (taggedSupport (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card) r).image
    (toVertex F K (n + 1))

/-- The complete literal fresh block of one birth-level request. -/
noncomputable def birthBlock
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) : Finset (Vertex F K) := by
  classical
  exact (taggedBlock (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card) r).image
    (toVertex F K (n + 1))

/-- Every minimal local type has a nonempty new block.
Its first vertex is the ordinal zero, with unchanged request tag. -/
noncomputable def birthRoot
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) : Vertex F K :=
  ⟨n, ⟨r, ⟨0, r.code.2.fresh_pos⟩⟩⟩

/-- The distinguished first vertex belongs to its complete
literal fresh request block. -/
theorem birthRoot_mem_block
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) :
    birthRoot F K n r ∈ birthBlock F K n r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Sum.inr ⟨r, ⟨0, r.code.2.fresh_pos⟩⟩, ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨⟨0, r.code.2.fresh_pos⟩, Finset.mem_univ _, rfl⟩
  · rfl

/-- The image of an actual named old support retains exactly
the birth names of its vertices in the previous finite stage. -/
theorem birthSupport_mem_of_old
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n)
    (u : (stage F K n).carrier) (hu : u ∈ r.support) :
    toVertex F K n u ∈ birthSupport F K n r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Sum.inl u, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · exact toVertex_old F K n u

/-- Every vertex in the literal old support was born at an earlier
level. This is needed for induction through the root dependencies. -/
theorem birthSupport_birth_lt
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n)
    {v : Vertex F K} (hv : v ∈ birthSupport F K n r) :
    v.1 < n := by
  classical
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
  obtain ⟨u, _, huw⟩ := Finset.mem_image.mp hw
  have hU : (toVertex F K n u).1 < n :=
    toVertex_birth_lt F K n u
  have hId :
      v = toVertex F K n u := by
    calc
      v = toVertex F K (n + 1) w := hwv.symm
      _ = toVertex F K (n + 1) (Sum.inl u) := by rw [huw]
      _ = toVertex F K n u := toVertex_old F K n u
  rw [hId]
  exact hU

/-- The local strict minimal extension is preserved and reflected
by the literal induced injection into the countable birth graph. -/
theorem birthLocal_minimal
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) :
    (countableGraph F K).toPredimension.IsMinimalDClosedStep
      (birthSupport F K n r)
      (birthSupport F K n r ∪ birthBlock F K n r) := by
  classical
  let G := (stage F K n).graph
  let Allowed := GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  let H := (stage F K (n + 1)).graph
  let j := toVertex F K (n + 1)
  have hAdj : ∀ u v : (stage F K (n + 1)).carrier,
      H.adj u v ↔ (countableGraph F K).adj (j u) (j v) := by
    intro u v
    exact (countableGraph_stage_induced F K (n + 1) u v).symm
  have hLocal := taggedLocal_minimal G Allowed bound r
  have hImage :=
    (H.minimalDClosedStep_image_iff
      (countableGraph F K) j (toVertex_injective F K (n + 1))
      hAdj (taggedSupport G Allowed bound r)
      (taggedSupport G Allowed bound r ∪
        taggedBlock G Allowed bound r)
      Finset.subset_union_left).mpr hLocal
  simpa only [birthSupport, birthBlock, Finset.image_union]
    using hImage

/-- The roots of all vertices are determined only by their
birth level and full request tag, not by their fresh ordinal. -/
noncomputable def rootOf
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Vertex F K → Vertex F K
  | ⟨n, ⟨r, _⟩⟩ => birthRoot F K n r

theorem rootOf_mem_birthClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (hs : IsBirthBlockClosed F K s)
    {v : Vertex F K} (hv : v ∈ s) :
    rootOf F K v ∈ s := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  exact (hs n r i hv).1 ⟨0, r.code.2.fresh_pos⟩

/-- The complete finite set of first vertices of blocks met by s.
For b-closed s it consists of vertices already in s. -/
noncomputable def rootsOf
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Finset (Vertex F K) :=
  s.image (rootOf F K)

theorem rootsOf_subset_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (hs : IsBirthBlockClosed F K s) :
    rootsOf F K s ⊆ s := by
  classical
  intro v hv
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
  rw [← huv]
  exact rootOf_mem_birthClosed F K s hs hu

end CFCoherentTower
end BigHrushovski
