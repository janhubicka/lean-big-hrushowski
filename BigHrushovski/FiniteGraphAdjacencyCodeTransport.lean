import BigHrushovski.FiniteGraphAdjacencyCode

/-!
# Naturality of complete finite adjacency matrices

The complete row-major adjacency matrix is unchanged when a
finite graph and its ordered coordinate list are transported
through an induced map. This elementary fact is shared by the
C_0 component codes and the C_F ordered local request codes.

The map need not be surjective, or even injective: the theorem
requires exact adjacency equivalence on all source pairs and
the coordinate list in the target to be the image of the source
list. In applications the named-support order embedding supplies
that coordinate-list equality separately.

This module makes no claim that the coordinate lists of arbitrary
ordered supports commute with a given map. That is the next
specific finite lifting obligation.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*}

/-- Mapping the two endpoints of every row-major coordinate pair
is the same as forming the square after mapping the vertex list. -/
private theorem flatMap_pairs_map
    (f : U → V) (xs ys : List U) :
    (xs.map f).flatMap
      (fun x => (ys.map f).map (fun y => (x, y))) =
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).map
      (fun p => (f p.1, f p.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [ih]
      simp [List.map_map, Function.comp_def]

/-- The row-major Cartesian square of a coordinate list commutes
with any vertex map, without requiring injectivity. -/
theorem adjacencyCoordinatePairs_map
    (f : U → V) (xs : List U) :
    adjacencyCoordinatePairs (xs.map f) =
      (adjacencyCoordinatePairs xs).map
        (fun p => (f p.1, f p.2)) := by
  unfold adjacencyCoordinatePairs
  exact flatMap_pairs_map f xs xs

/-- Complete adjacency-bit codes agree under an induced graph map
when the target coordinates are the images of the source
coordinates. Both edges and nonedges are reflected. -/
theorem orderedAdjacencyBits_induced
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (xs : List U) :
    orderedAdjacencyBits G xs =
      orderedAdjacencyBits H (xs.map f) := by
  classical
  unfold orderedAdjacencyBits
  rw [adjacencyCoordinatePairs_map]
  simp only [List.map_map]
  apply List.map_congr_left
  intro p hp
  by_cases h : G.adj p.1 p.2
  · have hh : H.adj (f p.1) (f p.2) := (hAdj _ _).mp h
    simp [h, hh]
  · have hh : ¬ H.adj (f p.1) (f p.2) :=
      fun h' => h ((hAdj _ _).mpr h')
    simp [h, hh]

/-- Special case for the actual pullback graph: the full ordered
matrix of a pullback is the matrix on the mapped coordinates. -/
theorem orderedAdjacencyBits_pullback_map
    (H : GraphOn V) (f : U → V) (xs : List U) :
    orderedAdjacencyBits (H.pullback f) xs =
      orderedAdjacencyBits H (xs.map f) :=
  orderedAdjacencyBits_induced (H.pullback f) H f
    (fun _ _ => Iff.rfl) xs

/-- Exact target coordinate equality is the only additional
input needed to transport the entire adjacency matrix. -/
theorem orderedAdjacencyBits_of_coordinate_eq
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (xs : List U) (ys : List V)
    (hCoords : ys = xs.map f) :
    orderedAdjacencyBits G xs =
      orderedAdjacencyBits H ys := by
  rw [hCoords]
  exact orderedAdjacencyBits_induced G H f hAdj xs

end GraphOn
end BigHrushovski
