import BigHrushovski.C0CoordinateGeneratedSubcode

/-!
# Cross-source rigidity for finite pointed natural-coordinate codes

Equality of two literal codes defined on different finite ordered carriers
determines a unique pointed map commuting with the increasing coordinate
labellings. The map is bijective and preserves and reflects every edge,
nonedge, and complete unary-value incidence. As both label maps are
increasing, the map also preserves the original orders.

This closes the finite mathematical justification for replacing pointed
isomorphism classes of triples (D,a,e) by literal codes. It does NOT
construct the countable coordinate host W or identify its permitted codes.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- A map into an injectively labelled target is uniquely determined
by its natural-number coordinate assignment. -/
theorem coordinateMap_unique
    (e : U ↪o ℕ) (f : V ↪o ℕ) (h k : U → V)
    (hh : ∀ u : U, f (h u) = e u)
    (hk : ∀ u : U, f (k u) = e u) : h = k := by
  funext u
  apply f.injective
  exact (hh u).trans (hk u).symm

/-- Equality of COMPLETE literal pointed codes, even with different
finite source carriers, gives the uniquely determined pointed
coordinate-preserving induced functional bijection. -/
theorem literalPointedCode_eq_crossSource
    (G : GraphOn U) (H : GraphOn V)
    (C : U → Finset U) (D : V → Finset V)
    (e : U ↪o ℕ) (f : V ↪o ℕ)
    (a : U) (b : V)
    (hCode : literalPointedCode G C e a =
      literalPointedCode H D f b) :
    ∃ h : U → V,
      Function.Bijective h ∧
      (∀ u : U, f (h u) = e u) ∧
      h a = b ∧
      (∀ u v : U, G.adj u v ↔ H.adj (h u) (h v)) ∧
      (∀ u v : U, v ∈ C u ↔ h v ∈ D (h u)) := by
  classical
  have hSupport : labelSupport e = labelSupport f :=
    congrArg LiteralPointedCode.support hCode
  have hExists (u : U) : ∃ v : V, f v = e u := by
    have hm : e u ∈ labelSupport f := by
      rw [← hSupport]
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
    exact ⟨v, hv⟩
  let h : U → V := fun u => Classical.choose (hExists u)
  have hCoord (u : U) : f (h u) = e u :=
    Classical.choose_spec (hExists u)
  have hInj : Function.Injective h := by
    intro u v huv
    apply e.injective
    calc
      e u = f (h u) := (hCoord u).symm
      _ = f (h v) := by rw [huv]
      _ = e v := hCoord v
  have hSurj : Function.Surjective h := by
    intro v
    have hm : f v ∈ labelSupport e := by
      rw [hSupport]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hm
    refine ⟨u, f.injective ?_⟩
    exact (hCoord u).trans hu
  have hPoint : e a = f b :=
    congrArg LiteralPointedCode.point hCode
  have hRoot : h a = b :=
    f.injective ((hCoord a).trans hPoint)
  have hGraph : coordinateAdjacencyPairs G e =
      coordinateAdjacencyPairs H f :=
    congrArg LiteralPointedCode.adjacencyPairs hCode
  have hAdj (u v : U) :
      G.adj u v ↔ H.adj (h u) (h v) := by
    rw [← mem_coordinateAdjacencyPairs_iff G e u v, hGraph]
    have hPair : (e u, e v) = (f (h u), f (h v)) := by
      rw [hCoord u, hCoord v]
    rw [hPair]
    exact mem_coordinateAdjacencyPairs_iff H f (h u) (h v)
  have hUnary : coordinateClosurePairs C e =
      coordinateClosurePairs D f :=
    congrArg LiteralPointedCode.closurePairs hCode
  have hC (u v : U) :
      v ∈ C u ↔ h v ∈ D (h u) := by
    rw [← mem_coordinateClosurePairs_iff C e u v, hUnary]
    have hPair : (e u, e v) = (f (h u), f (h v)) := by
      rw [hCoord u, hCoord v]
    rw [hPair]
    exact mem_coordinateClosurePairs_iff D f (h u) (h v)
  exact ⟨h, ⟨hInj, hSurj⟩, hCoord, hRoot, hAdj, hC⟩

end FiniteUnaryCoordinates
end BigHrushovski
