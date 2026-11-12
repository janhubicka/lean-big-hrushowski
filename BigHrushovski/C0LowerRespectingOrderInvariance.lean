import BigHrushovski.C0CanonicalOrderInvariance

/-!
# Track A: a closure-respecting component order preserves complete unary values

The canonical complete C₀ unary operation is unchanged when the
components are chronologically reordered, provided that

* the new index retains precisely the old component partition, and
* every vertex in a strict lower complete-unary value occurs in an
  earlier new component.

The proof does not assume that *all* unrelated pairs of components
retain their order. Instead it derives the necessary agreement on
each cross-component graph edge and applies the existing
`canonicalValue_eq_of_same_components_and_edge_orientation` theorem.

This is a reusable finite criterion for the fair countable component
enumeration. It makes no claim that a global fair component index has
already been constructed, nor that a within-component order is fixed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If an edge goes from a vertex to an earlier component, the earlier
endpoint belongs to the entire canonical value of the later endpoint.
The argument uses complete vertex-level reachability, not just a
numerical comparison or an immediate old-neighbour approximation. -/
theorem canonicalValue_mem_of_adj_earlier
    (G : GraphOn V) {n : ℕ} (κ : V → Fin n)
    {u v : V} (hEdge : G.adj u v)
    (hEarlier : (κ v).val < (κ u).val) :
    v ∈ canonicalValue G κ u := by
  apply (mem_canonicalValue_iff_vertexReach G κ u v).mpr
  exact VertexReach.next VertexReach.root
    (Or.inr ⟨hEdge, hEarlier⟩)

/-- Any chronological reindexing of the same whole components that
places every *strict* old complete-unary predecessor before its
generator has the same complete canonical C₀ unary operation.

In particular, one does NOT need to compare the order of unrelated
components; edge orientations follow from the old complete values. -/
theorem canonicalValue_eq_of_lower_respecting_order
    (G : GraphOn V) {n m : ℕ}
    (κ : V → Fin n) (κ₂ : V → Fin m)
    (hComponents : ∀ u v : V,
      κ u = κ v ↔ κ₂ u = κ₂ v)
    (hLowerEarlier : ∀ u v : V, κ u ≠ κ v →
      v ∈ canonicalValue G κ u →
      (κ₂ v).val < (κ₂ u).val)
    (x : V) :
    canonicalValue G κ x = canonicalValue G κ₂ x := by
  apply canonicalValue_eq_of_same_components_and_edge_orientation
    G κ κ₂ hComponents ?_ x
  intro u v hEdge
  constructor
  · intro hOldEarlier
    have hDifferent : κ u ≠ κ v := by
      intro heq
      have h := congrArg Fin.val heq
      omega
    exact hLowerEarlier u v hDifferent
      (canonicalValue_mem_of_adj_earlier G κ hEdge hOldEarlier)
  · intro hNewEarlier
    have hDifferent : κ u ≠ κ v := by
      intro heq
      have hNewEqual := (hComponents u v).mp heq
      have h := congrArg Fin.val hNewEqual
      omega
    have hDistinct : (κ u).val ≠ (κ v).val := by
      intro heq
      exact hDifferent (Fin.ext heq)
    rcases (show (κ v).val < (κ u).val ∨
        (κ u).val < (κ v).val by omega) with hWanted | hReverse
    · exact hWanted
    · have hVal : u ∈ canonicalValue G κ v :=
        canonicalValue_mem_of_adj_earlier G κ
          (G.symm u v hEdge) hReverse
      have hBackwards :=
        hLowerEarlier v u (Ne.symm hDifferent) hVal
      omega

end FiniteC0
end BigHrushovski
