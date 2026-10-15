import BigHrushovski.CFDClosedTransport
import BigHrushovski.CFLocalSupport

/-!
# Canonical old-neighbour d-closed support under induced images

The old support of a local minimal d-closed block is determined
intrinsically by graph adjacency and the least finite d-closed hull.
Both components of this definition transport exactly through any
induced injection on the finite ambient extension.

These are graph-theoretic assertions, with the target ambient set
taken to be the image of the source finite graph. They do not assert
d-closedness in an arbitrary larger target, or invariance of a
separately specified growth-function class.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*}
variable [DecidableEq U] [DecidableEq V]

/-- The complete set of old vertices meeting the fresh block
commutes with every induced graph map, without requiring any
particular bound on the size of the block. -/
theorem oldNeighbourSet_image
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V)
    (hAdj : ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v))
    (A B : Finset U) :
    (G.oldNeighbourSet A B).image f =
      H.oldNeighbourSet (A.image f) (B.image f) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨v, hvN, hfv⟩ := Finset.mem_image.mp hy
    change v ∈ A.filter
      (fun w => ∃ u : U, u ∈ B ∧ G.adj u w) at hvN
    obtain ⟨hvA, u, huB, hEdge⟩ := Finset.mem_filter.mp hvN
    change y ∈ (A.image f).filter
      (fun w => ∃ u : V, u ∈ B.image f ∧ H.adj u w)
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hvA, hfv⟩
    · refine ⟨f u, Finset.mem_image.mpr ⟨u, huB, rfl⟩, ?_⟩
      rw [← hfv]
      exact (hAdj u v).mp hEdge
  · intro hy
    change y ∈ (A.image f).filter
      (fun w => ∃ u : V, u ∈ B.image f ∧ H.adj u w) at hy
    obtain ⟨hyA, w, hwB, hEdge⟩ := Finset.mem_filter.mp hy
    obtain ⟨v, hvA, hfv⟩ := Finset.mem_image.mp hyA
    obtain ⟨u, huB, hfu⟩ := Finset.mem_image.mp hwB
    have hSourceEdge : G.adj u v := by
      apply (hAdj u v).mpr
      simpa only [hfu, hfv] using hEdge
    refine Finset.mem_image.mpr ⟨v, ?_, hfv⟩
    change v ∈ A.filter
      (fun z => ∃ q : U, q ∈ B ∧ G.adj q z)
    exact Finset.mem_filter.mpr ⟨hvA, ⟨u, huB, hSourceEdge⟩⟩

/-- The exact old-neighbour support, including every vertex
forced by finite strict d-closure, commutes with an induced
injection between corresponding finite ambient graphs. -/
theorem canonicalOldSupport_image
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v))
    (A B : Finset U) :
    (G.toPredimension.dClosedHull (G.oldNeighbourSet A B) A).image f =
      H.toPredimension.dClosedHull
        (H.oldNeighbourSet (A.image f) (B.image f))
        (A.image f) := by
  classical
  calc
    (G.toPredimension.dClosedHull (G.oldNeighbourSet A B) A).image f =
        H.toPredimension.dClosedHull
          ((G.oldNeighbourSet A B).image f) (A.image f) :=
      G.dClosedHull_image H f hf hAdj
        (G.oldNeighbourSet A B) A
        (G.oldNeighbourSet_subset A B)
    _ = H.toPredimension.dClosedHull
          (H.oldNeighbourSet (A.image f) (B.image f)) (A.image f) := by
      rw [G.oldNeighbourSet_image H f hAdj A B]

end GraphOn
end BigHrushovski
