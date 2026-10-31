import BigHrushovski.C0CoordinateHostGraph

/-!
# Finite closed restrictions for the C₀ coordinate host

The vertices of the coordinate host W are coded by pointed
one-generated finite unary closures. Restricting such a closure
to the one-generated closure of one of its vertices must recover
the COMPLETE unary values, not only include them.

This module isolates the finite subtype calculation, without
asserting that the whole quotient host W or its return embedding
has been constructed. It also verifies that the adjacency-based
unary value J commutes with closed restriction.
-/

namespace BigHrushovski

namespace FiniteUnaryCoordinates

variable {U : Type*} [DecidableEq U]

/-- The only closedness condition required for exact restriction of
an arbitrary finite set-valued unary function. -/
def ClosedUnder (C : U → Finset U) (s : Finset U) : Prop :=
  ∀ u ∈ s, C u ⊆ s

/-- The restriction of a complete unary value to a finite vertex
domain, represented on the subtype rather than on an unrelated
renumbering of the vertices. -/
noncomputable def restrictValue (C : U → Finset U) (s : Finset U)
    (u : s) : Finset s := by
  classical
  exact Finset.univ.filter (fun v => v.val ∈ C u.val)

theorem mem_restrictValue_iff
    (C : U → Finset U) (s : Finset U) (u v : s) :
    v ∈ restrictValue C s u ↔ v.val ∈ C u.val := by
  classical
  simp [restrictValue]

/-- Closedness of the domain makes restriction an equality of
COMPLETE vertex-valued functions. The subtype inclusion is not
silently assumed surjective onto the original ambient carrier. -/
theorem restrictValue_image
    (C : U → Finset U) (s : Finset U)
    (hs : ClosedUnder C s) (u : s) :
    (restrictValue C s u).image (Subtype.val : s → U) =
      C u.val := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_restrictValue_iff C s u w).mp hw
  · intro hv
    refine Finset.mem_image.mpr
      ⟨⟨v, hs u.val u.property hv⟩, ?_, rfl⟩
    exact (mem_restrictValue_iff C s u
      ⟨v, hs u.val u.property hv⟩).mpr hv

/-- The restricted values retain all one-generated closure
inclusions: a vertex inside C(u) has its entire closure in C(u). -/
theorem restrictValue_nested
    (C : U → Finset U) (s : Finset U)
    (hNested : ∀ u v : U, v ∈ C u → C v ⊆ C u)
    (u v : s) (hv : v ∈ restrictValue C s u) :
    restrictValue C s v ⊆ restrictValue C s u := by
  intro w hw
  apply (mem_restrictValue_iff C s u w).mpr
  exact hNested u.val v.val
    ((mem_restrictValue_iff C s u v).mp hv)
    ((mem_restrictValue_iff C s v w).mp hw)

/-- The induced graph on a finite closed domain; this definition
does not introduce or forget graph edges. -/
def restrictGraph (G : GraphOn U) (s : Finset U) : GraphOn s where
  adj u v := G.adj u.val v.val
  symm u v h := G.symm u.val v.val h
  irrefl u := G.irrefl u.val

theorem restrictGraph_adj_iff
    (G : GraphOn U) (s : Finset U) (u v : s) :
    (restrictGraph G s).adj u v ↔ G.adj u.val v.val :=
  Iff.rfl

/-- The back-adjacency unary value commutes with restriction,
provided the COMPLETE closure value is restricted on the same
literal finite domain. No closedness is needed for the equality
*inside* the subtype; closedness enters its image equality. -/
theorem restrictBackAdjacencyValue
    (G : GraphOn U) (C : U → Finset U)
    (s : Finset U) (u : s) :
    (restrictGraph G s).backAdjacencyValue
      (fun v : s => restrictValue C s v) u =
    restrictValue (G.backAdjacencyValue C) s u := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hC, hAdj⟩ :=
      ((restrictGraph G s).mem_backAdjacencyValue_iff
        (fun w : s => restrictValue C s w) u v).mp hv
    apply (mem_restrictValue_iff
      (G.backAdjacencyValue C) s u v).mpr
    apply (G.mem_backAdjacencyValue_iff C u.val v.val).mpr
    exact ⟨(mem_restrictValue_iff C s u v).mp hC, hAdj⟩
  · intro hv
    obtain ⟨hC, hAdj⟩ :=
      (G.mem_backAdjacencyValue_iff C u.val v.val).mp
        ((mem_restrictValue_iff
          (G.backAdjacencyValue C) s u v).mp hv)
    apply ((restrictGraph G s).mem_backAdjacencyValue_iff
      (fun w : s => restrictValue C s w) u v).mpr
    exact ⟨(mem_restrictValue_iff C s u v).mpr hC, hAdj⟩

end FiniteUnaryCoordinates

namespace FiniteCatalogue

open FiniteUnaryCoordinates

/-- Every canonical one-generated C₀ unary closure is itself a
closed finite domain, by transitivity of the ancestor relation. -/
theorem genericC0OneGenerated_isClosed (a : ℕ) :
    ClosedUnder genericC0UnaryClosure (genericC0UnaryClosure a) := by
  intro u hu
  exact genericC0UnaryClosure_nested hu

/-- All closure values inside a finite canonical one-generated closure
are complete after restriction. These are exactly the restricted
C-values which the coordinate-host codes must retain. -/
theorem genericC0OneGenerated_C_image (a : ℕ)
    (u : genericC0UnaryClosure a) :
    (restrictValue genericC0UnaryClosure (genericC0UnaryClosure a) u).image
      (Subtype.val : genericC0UnaryClosure a → ℕ) =
        genericC0UnaryClosure u.val :=
  restrictValue_image genericC0UnaryClosure (genericC0UnaryClosure a)
    (genericC0OneGenerated_isClosed a) u

/-- All J-values inside a canonical one-generated closure are likewise
complete: the graph is recovered from these full unary values. -/
theorem genericC0OneGenerated_J_image (a : ℕ)
    (u : genericC0UnaryClosure a) :
    (restrictValue genericC0BackAdjacency (genericC0UnaryClosure a) u).image
      (Subtype.val : genericC0UnaryClosure a → ℕ) =
        genericC0BackAdjacency u.val := by
  apply restrictValue_image
  intro v hv
  intro w hw
  have hC : w ∈ genericC0UnaryClosure v :=
    ((mem_genericC0BackAdjacency_iff v w).mp hw).1
  exact (genericC0UnaryClosure_nested hv) hC

/-- On a concrete closed finite C₀ domain, the restricted graph's
back-adjacency value is precisely the restricted ambient J value. -/
theorem genericC0OneGenerated_restrict_J (a : ℕ)
    (u : genericC0UnaryClosure a) :
    (restrictGraph genericTwoSparseGraph (genericC0UnaryClosure a)).
      backAdjacencyValue
        (fun v => restrictValue genericC0UnaryClosure
          (genericC0UnaryClosure a) v) u =
      restrictValue genericC0BackAdjacency
        (genericC0UnaryClosure a) u :=
  restrictBackAdjacencyValue genericTwoSparseGraph
    genericC0UnaryClosure (genericC0UnaryClosure a) u

end FiniteCatalogue
end BigHrushovski
