import BigHrushovski.CFNormalizedLocalType
import BigHrushovski.CFGrowthClass
import BigHrushovski.CFLocalSupportTransport

/-!
# Extract a complete split C_F local graph from finite vertex subsets

Given an arbitrary finite graph G and disjoint finite subsets P,B
of its vertices, we represent the induced graph on P ∪ B by the
disjoint carrier P_subtype ⊕ B_subtype. The map to the original
graph remembers the *actual* vertices and is injective because
P and B are disjoint.

This complete induced representation preserves C_F growth
membership, minimal strict d-closedness of P <_d P ∪ B,
and the least d-closed hull of all old neighbours of B.
It also agrees with the graph induced on the named old set P.

The canonical-support lemma supplies the minimal-step and
exact-support hypotheses when P is chosen as the old
d-closure of the neighbours of a minimal increment A <_d C.
Neither the size bound nor the subsequent map into a
particular countable stage is assumed here.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev OldCarrier (V : Type*) (P : Finset V) := {v : V // v ∈ P}
abbrev FreshCarrier (V : Type*) (B : Finset V) := {v : V // v ∈ B}

/-- Forget whether a vertex lies in the named old set or
the chosen new block. -/
def splitValue (P B : Finset V) :
    Sum (OldCarrier V P) (FreshCarrier V B) → V
  | Sum.inl p => p.val
  | Sum.inr b => b.val

/-- The split map is injective when the old and fresh
vertices are disjoint in the original graph. -/
theorem splitValue_injective
    (P B : Finset V) (hDisj : Disjoint P B) :
    Function.Injective (splitValue P B) := by
  intro x y hxy
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          exact congrArg Sum.inl (Subtype.ext hxy)
      | inr b =>
          have heq : p.val = b.val := hxy
          have hpB : p.val ∈ B := by
            rw [heq]
            exact b.property
          exact False.elim
            ((Finset.disjoint_left.mp hDisj) p.property hpB)
  | inr b =>
      cases y with
      | inl p =>
          have heq : b.val = p.val := hxy
          have hpB : p.val ∈ B := by
            rw [← heq]
            exact b.property
          exact False.elim
            ((Finset.disjoint_left.mp hDisj) p.property hpB)
      | inr c =>
          exact congrArg Sum.inr (Subtype.ext hxy)

/-- The entire induced graph on P∪B, with its old/new
partition now literally recorded in the vertex type. -/
noncomputable def splitGraph (G : GraphOn V)
    (P B : Finset V) :
    GraphOn (Sum (OldCarrier V P) (FreshCarrier V B)) :=
  G.pullback (splitValue P B)

theorem splitGraph_adj_iff (G : GraphOn V)
    (P B : Finset V)
    (x y : Sum (OldCarrier V P) (FreshCarrier V B)) :
    (splitGraph G P B).adj x y ↔
      G.adj (splitValue P B x) (splitValue P B y) :=
  Iff.rfl

/-- The old side of the split graph maps onto the
original *literal* subset P. -/
theorem splitOld_image (P B : Finset V) :
    (actualOld (OldCarrier V P) (FreshCarrier V B)).image
      (splitValue P B) = P := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
    obtain ⟨p, _, hpz⟩ := Finset.mem_image.mp hz
    subst z
    change p.val = v at hzv
    rw [← hzv]
    exact p.property
  · intro hv
    refine Finset.mem_image.mpr
      ⟨Sum.inl ⟨v, hv⟩, ?_, rfl⟩
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

/-- The fresh side maps onto B without renaming or
identifying any vertices. -/
theorem splitFresh_image (P B : Finset V) :
    (actualFresh (OldCarrier V P) (FreshCarrier V B)).image
      (splitValue P B) = B := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
    obtain ⟨b, _, hbz⟩ := Finset.mem_image.mp hz
    subst z
    change b.val = v at hzv
    rw [← hzv]
    exact b.property
  · intro hv
    refine Finset.mem_image.mpr
      ⟨Sum.inr ⟨v, hv⟩, ?_, rfl⟩
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

private theorem actualOld_union_actualFresh
    (P B : Finset V) :
    actualOld (OldCarrier V P) (FreshCarrier V B) ∪
      actualFresh (OldCarrier V P) (FreshCarrier V B) =
      (Finset.univ : Finset
        (Sum (OldCarrier V P) (FreshCarrier V B))) := by
  classical
  ext x
  cases x with
  | inl p => simp [actualOld, actualFresh]
  | inr b => simp [actualOld, actualFresh]

/-- The whole split carrier is exactly the induced
vertex set P∪B in the original finite graph. -/
theorem splitUniv_image (P B : Finset V) :
    ((Finset.univ : Finset
      (Sum (OldCarrier V P) (FreshCarrier V B))).image
        (splitValue P B)) = P ∪ B := by
  classical
  rw [← actualOld_union_actualFresh P B,
    Finset.image_union, splitOld_image, splitFresh_image]

/-- The split local graph agrees with the actual graph on
its old named subtype. -/
theorem splitGraph_old_adj_iff
    (G : GraphOn V) (P B : Finset V)
    (p q : OldCarrier V P) :
    (splitGraph G P B).adj (Sum.inl p) (Sum.inl q) ↔
      (G.pullback Subtype.val).adj p q :=
  Iff.rfl

/-- Exact preservation of the growth-function class
for a split induced local graph. -/
theorem splitGraph_growthSparse_iff
    (G : GraphOn V) (F : ℕ → ℝ)
    (P B : Finset V) (hDisj : Disjoint P B) :
    (splitGraph G P B).IsGrowthSparse F Finset.univ ↔
      G.IsGrowthSparse F (P ∪ B) := by
  classical
  have h :=
    (splitGraph G P B).growthSparse_image_iff
      G F (splitValue P B)
      (splitValue_injective P B hDisj)
      (fun x y => splitGraph_adj_iff G P B x y)
      (Finset.univ : Finset
        (Sum (OldCarrier V P) (FreshCarrier V B)))
  rw [splitUniv_image] at h
  exact h.symm

/-- A minimal strict d-closed step over P remains minimal
on its complete split carrier. -/
theorem splitGraph_minimal
    (G : GraphOn V) (P B : Finset V)
    (hDisj : Disjoint P B)
    (hMin : G.toPredimension.IsMinimalDClosedStep P (P ∪ B)) :
    (splitGraph G P B).toPredimension.IsMinimalDClosedStep
      (actualOld (OldCarrier V P) (FreshCarrier V B))
      Finset.univ := by
  classical
  apply ((splitGraph G P B).minimalDClosedStep_image_iff
    G (splitValue P B)
    (splitValue_injective P B hDisj)
    (fun x y => splitGraph_adj_iff G P B x y)
    (actualOld (OldCarrier V P) (FreshCarrier V B))
    Finset.univ (Finset.subset_univ _)).mp
  rw [splitOld_image, splitUniv_image]
  exact hMin

/-- The d-closed hull of the old neighbours is exact
also in the split local graph. -/
theorem splitGraph_exactSupport
    (G : GraphOn V) (P B : Finset V)
    (hDisj : Disjoint P B)
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet P B) P = P) :
    (splitGraph G P B).toPredimension.dClosedHull
      ((splitGraph G P B).oldNeighbourSet
        (actualOld (OldCarrier V P) (FreshCarrier V B))
        (actualFresh (OldCarrier V P) (FreshCarrier V B)))
      (actualOld (OldCarrier V P) (FreshCarrier V B)) =
        actualOld (OldCarrier V P) (FreshCarrier V B) := by
  classical
  let f := splitValue P B
  have hf : Function.Injective f := splitValue_injective P B hDisj
  have hImage := (splitGraph G P B).canonicalOldSupport_image
    G f hf (fun x y => splitGraph_adj_iff G P B x y)
    (actualOld (OldCarrier V P) (FreshCarrier V B))
    (actualFresh (OldCarrier V P) (FreshCarrier V B))
  rw [splitOld_image, splitFresh_image] at hImage
  apply Finset.image_injective hf
  calc
    ((splitGraph G P B).toPredimension.dClosedHull
      ((splitGraph G P B).oldNeighbourSet
        (actualOld (OldCarrier V P) (FreshCarrier V B))
        (actualFresh (OldCarrier V P) (FreshCarrier V B)))
      (actualOld (OldCarrier V P) (FreshCarrier V B))).image f =
        G.toPredimension.dClosedHull (G.oldNeighbourSet P B) P := hImage
    _ = P := hSupport
    _ = (actualOld (OldCarrier V P) (FreshCarrier V B)).image f :=
      (splitOld_image P B).symm

end CFLocalCatalogue
end BigHrushovski
