import BigHrushovski.C0CoordinateWellSupportedCode

/-!
# Finite fibres of complete finite coordinate codes

A complete literal pointed code has finite support, but the raw record
need not have any finite bound on its relation pairs. This is why the
WellSupported invariant was introduced separately.

With that invariant, and a fixed finite coordinate range, there are
only finitely many possible FULL pointed codes: the support is one of
finitely many subsets of the range, the point lies in that range, and
each complete adjacency/C matrix is one of finitely many subsets of
the square of the range.

We make the argument explicit via an injective map to a finite type.
No permitted-age predicate, graph sparsity, or return map is assumed.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- A complete pointed code whose whole support and both complete
matrices are contained in a fixed initial coordinate interval. -/
def BoundedWellSupportedCode (N : ℕ) : Type :=
  {q : LiteralPointedCode //
    q.WellSupported ∧ q.support ⊆ Finset.range N}

/-- For each fixed coordinate bound, there are finitely many possible
complete supported pointed records. This is the finite-fibre fact
needed for a future component enumeration of the coordinate host W.

The proof retains all four data fields and does not quotient by an
unpointed local type or discard negative incidence information. -/
theorem finite_boundedWellSupportedCode (N : ℕ) :
    Finite (BoundedWellSupportedCode N) := by
  classical
  let supports : Finset (Finset ℕ) := (Finset.range N).powerset
  let pairs : Finset (Finset (ℕ × ℕ)) :=
    ((Finset.range N).product (Finset.range N)).powerset
  let codes :
      Finset (Finset ℕ × (ℕ ×
        (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)))) :=
    supports.product ((Finset.range N).product
      (pairs.product pairs))
  let encode : BoundedWellSupportedCode N → codes := fun q => by
    let h := q.val.wellSupported_bounded q.property.1 N
      q.property.2
    refine ⟨(q.val.support,
      (q.val.point, (q.val.adjacencyPairs, q.val.closurePairs))), ?_⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_powerset.mpr q.property.2
    · apply Finset.mem_product.mpr
      constructor
      · exact h.1
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_powerset.mpr h.2.1,
          Finset.mem_powerset.mpr h.2.2⟩
  have hInjective : Function.Injective encode := by
    intro q r h
    have hFields := congrArg Subtype.val h
    apply Subtype.ext
    apply LiteralPointedCode.ext
    · exact congrArg Prod.fst hFields
    · exact congrArg (fun t => t.2.1) hFields
    · exact congrArg (fun t => t.2.2.1) hFields
    · exact congrArg (fun t => t.2.2.2) hFields
  exact Finite.of_injective encode hInjective

/-- A finite enumeration of every bounded, fully supported coordinate
record exists. In particular there cannot be infinitely many raw
component codes with bounded coordinate support once both matrices
are required to stay within that support. -/
noncomputable def boundedWellSupportedCodeFintype (N : ℕ) :
    Fintype (BoundedWellSupportedCode N) := by
  letI : Finite (BoundedWellSupportedCode N) :=
    finite_boundedWellSupportedCode N
  exact Fintype.ofFinite _

end FiniteUnaryCoordinates
end BigHrushovski
