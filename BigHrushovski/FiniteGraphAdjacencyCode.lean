import BigHrushovski.InducedEmbedding

/-!
# Complete adjacency codes of finite graphs

The entire adjacency matrix of a graph on a finite vertex type can be
read as a list of zero/one bits in any fixed complete coordinate
enumeration. This encoding is injective, even if the list repeats
some vertices, as long as it contains every vertex at least once.

This elementary reusable fact will certify that a normalized
ordered local C_F graph code distinguishes every graph over a fixed
literal support and fixed fresh size. It can also be used for
finite C_0 component/type codes.

Nothing about graph predimension, C_F growth, or order of unrelated
vertex blocks is needed.
-/

namespace BigHrushovski
namespace GraphOn

variable {W : Type*}

/-- The ordered Cartesian square of a coordinate list, read
row by row. -/
def adjacencyCoordinatePairs (xs : List W) : List (W × W) :=
  xs.flatMap (fun u => xs.map (fun v => (u,v)))

/-- Complete ordered zero/one matrix of a graph, with no
restriction to only old-fresh edges. -/
noncomputable def orderedAdjacencyBits
    (G : GraphOn W) (xs : List W) : List Nat := by
  classical
  exact (adjacencyCoordinatePairs xs).map
    (fun uv => if G.adj uv.1 uv.2 then 1 else 0)

/-- If two maps have identical value lists on a fixed sequence,
their values agree at every coordinate occurring in that list. -/
private theorem listMap_eq_on_mem
    {α β : Type*} (f g : α → β) :
    ∀ xs : List α, xs.map f = xs.map g →
      ∀ u : α, u ∈ xs → f u = g u
  | [], _, u, hu => by cases hu
  | v :: vs, h, u, hu => by
      have hHead : f v = g v := (List.cons.inj h).1
      have hTail : vs.map f = vs.map g := (List.cons.inj h).2
      rcases List.mem_cons.mp hu with rfl | huTail
      · exact hHead
      · exact listMap_eq_on_mem f g vs hTail u huTail

/-- Every ordered pair occurs in the Cartesian-square
enumeration if both its endpoints occur in the coordinate list. -/
theorem mem_adjacencyCoordinatePairs
    (xs : List W) {u v : W}
    (hu : u ∈ xs) (hv : v ∈ xs) :
    (u,v) ∈ adjacencyCoordinatePairs xs := by
  unfold adjacencyCoordinatePairs
  apply List.mem_flatMap.mpr
  refine ⟨u, hu, ?_⟩
  exact List.mem_map.mpr ⟨v, hv, rfl⟩

/-- The full adjacency-bit code of any complete coordinate
list distinguishes finite simple graphs exactly. The proof
uses both edge and nonedge information; a list of positive
edges alone would also suffice, but is less convenient for
the manuscript's ordered graph code. -/
theorem orderedAdjacencyBits_injective_of_complete
    (xs : List W) (hComplete : ∀ u : W, u ∈ xs) :
    Function.Injective (fun G : GraphOn W => orderedAdjacencyBits G xs) := by
  classical
  intro G H hCode
  have hMatrix :
      ∀ u v : W,
        (if G.adj u v then (1:ℕ) else 0) =
          (if H.adj u v then (1:ℕ) else 0) := by
    intro u v
    have hEntries :=
      listMap_eq_on_mem
        (fun uv : W × W => if G.adj uv.1 uv.2 then (1:ℕ) else 0)
        (fun uv : W × W => if H.adj uv.1 uv.2 then (1:ℕ) else 0)
        (adjacencyCoordinatePairs xs) hCode
    exact hEntries (u,v)
      (mem_adjacencyCoordinatePairs xs (hComplete u) (hComplete v))
  have hAdj : G.adj = H.adj := by
    funext u v
    apply propext
    constructor
    · intro hg
      by_contra hh
      have hb := hMatrix u v
      simp [hg, hh] at hb
    · intro hh
      by_contra hg
      have hb := hMatrix u v
      simp [hg, hh] at hb
  have hGraphOn : Function.Injective (fun g : GraphOn W => g.adj) := by
    intro G' H' heq
    cases G'
    cases H'
    cases heq
    rfl
  exact hGraphOn hAdj

end GraphOn
end BigHrushovski
