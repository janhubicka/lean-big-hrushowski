import BigHrushovski.C0FiniteCanonicalRestriction

/-!
# Canonical C0 unary values do not change when later blocks are attached

Every direct C0 dependency points to a strictly earlier component.
Therefore an ancestor of a component has no larger index.
The canonical unary closure of any vertex in an old prefix A_k
is completely contained in A_k.

The previous exact finite restriction theorem now identifies the
canonical unary value computed inside the induced old prefix with
the *entire* value computed in the final finite graph. This is the
temporal persistence invariant used when a new minimal strong block
is appended to an existing finite functional presentation.

The result does not assume 2-sparsity, strongness, or minimality of
the graph blocks; it is a purely combinatorial consequence of the
backward dependency definition.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- Reachability along decreasing canonical component dependencies
cannot increase the component index. -/
theorem canonicalAncestor_index_le
    (G : GraphOn V) (κ : V → Fin n)
    {i j : Fin n}
    (h : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) i j) :
    j.val ≤ i.val := by
  induction h with
  | root =>
      exact le_refl _
  | @step u v hu hDep ih =>
      have hLt : v.val < u.val := hDep.1
      omega

/-- No vertex inserted in a later component can enter the unary
closure of a vertex already present in the kth prefix. -/
theorem canonicalValue_subset_oldStage
    (G : GraphOn V) (κ : V → Fin n)
    (k : ℕ) (u : V)
    (hu : u ∈ oldStage κ k) :
    canonicalValue G κ u ⊆ oldStage κ k := by
  intro v hv
  have hOld : (κ u).val < k :=
    (mem_oldStage_iff κ k u).mp hu
  have hLe : (κ v).val ≤ (κ u).val :=
    canonicalAncestor_index_le G κ
      ((mem_canonicalValue_iff G κ u v).mp hv)
  exact (mem_oldStage_iff κ k v).mpr (by omega)

/-- Every indexed finite prefix is closed under the named complete
backward-reachability function. -/
theorem canonicalValue_oldStage_closed
    (G : GraphOn V) (κ : V → Fin n) (k : ℕ) :
    G.IsClosedUnderValues
      (canonicalValue G κ) (oldStage κ k) := by
  intro u hu
  exact canonicalValue_subset_oldStage G κ k u hu

/-- Computing the full canonical unary value inside an old prefix
gives exactly its value in the final graph: future components make
no change to any previously defined unary value. -/
theorem canonicalValue_oldStage_restrict_image
    (G : GraphOn V) (κ : V → Fin n) (k : ℕ)
    (u : {v : V // v ∈ oldStage κ k}) :
    (canonicalValue
      (G.pullback
        (Subtype.val : {v : V // v ∈ oldStage κ k} → V))
      (restrictIndex κ (oldStage κ k)) u).image
        (Subtype.val : {v : V // v ∈ oldStage κ k} → V) =
      canonicalValue G κ u.val :=
  canonicalValue_restrict_image G κ (oldStage κ k)
    (canonicalValue_oldStage_closed G κ k) u

end FiniteC0
end BigHrushovski
