import BigHrushovski.CFBatchDClosed
import BigHrushovski.CFGrowthClass

/-!
# The finite tagged C_F stage belongs to the growth class,
# conditional on the published d-closed free-amalgamation property

The graph construction and strict d-closedness of every tagged prefix
are already verified. What remains for the *growth-function class*
is to show that membership is preserved by each permitted free join.

We now do so by induction over all finite request tags.  Every old
support P is d-closed in the current prefix by transitivity, every
local code is induced in its exact tagged copy, and no fresh vertex
has an old neighbour outside P. This realizes the hypotheses of
the stated class-level free-amalgamation property.

The hypotheses are deliberately separate:
  * the finite old graph U satisfies δ(X) >= F(|X|);
  * every permitted normalized local code satisfies the same bound;
  * the restricted growth class is closed under d-closed free joins.

The third clause is not proved from monotonicity of F; it is a
standing hypothesis of the C_F construction. This theorem is still
finite; it does not construct the countable generic or prove the
fair extension schedule, block-root recovery or monoid claims.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Literal old vertices belong to every finite tagged prefix. -/
theorem taggedOld_subset_prefix
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (done : Finset (Requests G Allowed bound)) :
    taggedOldDomain G Allowed bound ⊆
      taggedBatchPrefix G Allowed bound done := by
  intro x hx
  change x ∈ taggedOldDomain G Allowed bound ∪
    done.biUnion (taggedBlock G Allowed bound)
  exact Finset.mem_union.mpr (Or.inl hx)

/-- The old graph's growth inequality is preserved inside the
actual induced old part of the full tagged batch graph. -/
theorem taggedOld_growthSparse
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (F : ℕ → ℝ)
    (hOld : G.IsGrowthSparse F (Finset.univ : Finset U)) :
    (levelGraph G Allowed bound).IsGrowthSparse F
      (taggedOldDomain G Allowed bound) := by
  classical
  have h := (G.growthSparse_image_iff
    (levelGraph G Allowed bound) F
    (Sum.inl : U → LevelCarrier G Allowed bound)
    Sum.inl_injective
    (fun x y => (levelGraph_old_iff G Allowed bound x y).symm)
    Finset.univ).mpr hOld
  change (levelGraph G Allowed bound).IsGrowthSparse F
    (taggedOldDomain G Allowed bound) at h
  exact h

/-- Every complete local growth-class code satisfies the growth
inequality on the corresponding finite **induced tagged copy**,
not merely on its support boundary. -/
theorem taggedLocal_growthSparse
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (F : ℕ → ℝ)
    (r : Requests G Allowed bound)
    (hCode : r.code.2.graph.IsGrowthSparse F Finset.univ) :
    (levelGraph G Allowed bound).IsGrowthSparse F
      (taggedSupport G Allowed bound r ∪
        taggedBlock G Allowed bound r) := by
  classical
  have h := (r.code.2.graph.growthSparse_image_iff
    (levelGraph G Allowed bound) F
    (localTag G Allowed bound r)
    (localTag_injective G Allowed bound r)
    (fun x y => (levelGraph_local_adj_iff G Allowed bound r x y).symm)
    Finset.univ).mpr hCode
  rw [localUniv_image_eq_support_union_block] at h
  exact h

/-- The growth condition on the full tagged batch is preserved
during **every** initial finite list of attached requests, provided
the d-closed free-amalgamation property holds for the restricted
class on this graph. -/
theorem taggedBatchPrefix_growthSparse
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (F : ℕ → ℝ)
    (hOld : G.IsGrowthSparse F (Finset.univ : Finset U))
    (hCodes : ∀ r : Requests G Allowed bound,
      r.code.2.graph.IsGrowthSparse F Finset.univ)
    (hFree : (levelGraph G Allowed bound).GrowthClosedUnderDClosedFreeJoins F)
    (done : Finset (Requests G Allowed bound)) :
    (levelGraph G Allowed bound).IsGrowthSparse F
      (taggedBatchPrefix G Allowed bound done) := by
  classical
  let H := levelGraph G Allowed bound
  induction done using Finset.induction_on with
  | empty =>
      simpa [taggedBatchPrefix] using
        (taggedOld_growthSparse G Allowed bound F hOld)
  | @insert r done hr ih =>
      let A := taggedBatchPrefix G Allowed bound done
      let P := taggedSupport G Allowed bound r
      let B := taggedBlock G Allowed bound r
      let E := P ∪ B
      have hPA : P ⊆ A :=
        (taggedSupport_subset_old G Allowed bound r).trans
          (taggedOld_subset_prefix G Allowed bound done)
      have hPClosed : H.toPredimension.IsDClosed P A :=
        H.toPredimension.dclosed_trans
          (taggedSupport_dClosed_old G Allowed bound r)
          (taggedOld_dClosed_prefix G Allowed bound done)
      have hEClosed : H.toPredimension.IsDClosed P E :=
        (taggedLocal_minimal G Allowed bound r).1
      have hDisj : Disjoint A B :=
        taggedBlock_disjoint_prefix G Allowed bound done r hr
      have hBack : ∀ x ∈ B, ∀ y ∈ A, H.adj x y → y ∈ P :=
        taggedBlock_backNeighbours_prefix G Allowed bound done r hr
      have hNo : H.NoCrossEdges A E :=
        H.noCross_of_backNeighbours A P B hPA hBack
      have hCap : A ∩ E = P := by
        apply le_antisymm
        · intro v hv
          obtain ⟨hvA, hvE⟩ := Finset.mem_inter.mp hv
          rcases Finset.mem_union.mp hvE with hvP | hvB
          · exact hvP
          · exact False.elim
              ((Finset.disjoint_left.mp hDisj) hvA hvB)
        · intro v hvP
          exact Finset.mem_inter.mpr
            ⟨hPA hvP, Finset.mem_union.mpr (Or.inl hvP)⟩
      have hE : H.IsGrowthSparse F E :=
        taggedLocal_growthSparse G Allowed bound F r (hCodes r)
      have hJoin : H.IsGrowthSparse F (A ∪ E) :=
        H.growthSparse_free_join F hFree P A E
          hCap hNo hPClosed hEClosed ih hE
      have hUnion : A ∪ E = A ∪ B := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_union.mp hv with hvA | hvE
          · exact Finset.mem_union.mpr (Or.inl hvA)
          · rcases Finset.mem_union.mp hvE with hvP | hvB
            · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
            · exact Finset.mem_union.mpr (Or.inr hvB)
        · intro hv
          rcases Finset.mem_union.mp hv with hvA | hvB
          · exact Finset.mem_union.mpr (Or.inl hvA)
          · exact Finset.mem_union.mpr
              (Or.inr (Finset.mem_union.mpr (Or.inr hvB)))
      change H.IsGrowthSparse F
        (taggedBatchPrefix G Allowed bound (insert r done))
      rw [taggedBatchPrefix_insert]
      simpa only [hUnion] using hJoin

/-- The entire finite simultaneous tagged stage satisfies the exact
real-valued growth-function lower bound, **conditional on** the
class-level d-closed free-amalgamation hypothesis and membership
of all original/locally permitted code graphs. -/
theorem levelGraph_growthSparse_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (F : ℕ → ℝ)
    (hOld : G.IsGrowthSparse F (Finset.univ : Finset U))
    (hCodes : ∀ r : Requests G Allowed bound,
      r.code.2.graph.IsGrowthSparse F Finset.univ)
    (hFree : (levelGraph G Allowed bound).GrowthClosedUnderDClosedFreeJoins F) :
    (levelGraph G Allowed bound).IsGrowthSparse F
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  have h := taggedBatchPrefix_growthSparse G Allowed bound
    F hOld hCodes hFree
    (Finset.univ : Finset (Requests G Allowed bound))
  rw [taggedBatchPrefix_univ] at h
  exact h

/-- Use the *actual* growth-function class itself as the
admissibility predicate for complete finite ordered local codes.
The type and size bounds are supplied independently. -/
def GrowthAllowedLocal (F : ℕ → ℝ) : AllowedLocal U :=
  fun P n K => K.IsGrowthSparse F Finset.univ

/-- When permitted local codes are selected precisely from the
growth class, the code-membership hypothesis in the finite
tagged-batch theorem is automatic. The separate free-amalgamation
hypothesis is retained explicitly. -/
theorem levelGraph_growthSparse_of_growth_allowed
    (G : GraphOn U)
    (bound : Finset U → ℕ)
    (F : ℕ → ℝ)
    (hOld : G.IsGrowthSparse F (Finset.univ : Finset U))
    (hFree : (levelGraph G (GrowthAllowedLocal F) bound).GrowthClosedUnderDClosedFreeJoins F) :
    (levelGraph G (GrowthAllowedLocal F) bound).IsGrowthSparse F
      (Finset.univ : Finset
        (LevelCarrier G (GrowthAllowedLocal F) bound)) := by
  apply levelGraph_growthSparse_full G (GrowthAllowedLocal F)
    bound F hOld ?_ hFree
  intro r
  exact r.code.2.allowed

end CFStageCatalogue
end BigHrushovski
