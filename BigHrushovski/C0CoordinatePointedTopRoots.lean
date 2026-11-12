import BigHrushovski.C0CoordinatePointedAgeCode

/-!
# Generator-independent keys for complete finite pointed coordinate codes

A W closure-component is not to be enumerated once for EACH choice
of a top generator: different root coordinates on the same complete
unpointed local code generate each other. This is a FINITE statement
about literal complete codes, before construction of the global W.

The unpointed key retains the literal coordinate support, every graph
pair (hence nonedges) and every named unary C-incidence. The point
coordinate is omitted, but not the complete unary data. The conclusions
use genuine generated-point conditions, not arbitrary pointed records.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Complete unpointed finite-coordinate code of a local diagram.
Its support, adjacency matrix and complete C-matrix determine the
diagram; the choice of a generating top vertex is irrelevant. -/
def LiteralPointedCode.unpointedKey (q : LiteralPointedCode) :
    Finset ℕ × (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) :=
  (q.support, (q.adjacencyPairs, q.closurePairs))

/-- The unpointed key remembers ALL three finite data fields exactly. -/
theorem LiteralPointedCode.unpointedKey_eq_iff
    (q r : LiteralPointedCode) :
    q.unpointedKey = r.unpointedKey ↔
      q.support = r.support ∧
      q.adjacencyPairs = r.adjacencyPairs ∧
      q.closurePairs = r.closurePairs := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,
      congrArg (fun t => t.2.1) h,
      congrArg (fun t => t.2.2) h⟩
  · rintro ⟨hS,hA,hC⟩
    simp [LiteralPointedCode.unpointedKey,hS,hA,hC]

/-- Equal complete unpointed keys reflect all pairs and their
absence, not only preservation of positive graph incidences. -/
theorem LiteralPointedCode.unpointedKey_adj_iff
    (q r : LiteralPointedCode)
    (h : q.unpointedKey = r.unpointedKey)
    (u v : ℕ) :
    (u,v) ∈ q.adjacencyPairs ↔ (u,v) ∈ r.adjacencyPairs := by
  have hA : q.adjacencyPairs = r.adjacencyPairs :=
    ((q.unpointedKey_eq_iff r).mp h).2.1
  rw [hA]

/-- The same exact reflection for every complete C-incidence. -/
theorem LiteralPointedCode.unpointedKey_C_iff
    (q r : LiteralPointedCode)
    (h : q.unpointedKey = r.unpointedKey)
    (u v : ℕ) :
    (u,v) ∈ q.closurePairs ↔ (u,v) ∈ r.closurePairs := by
  have hC : q.closurePairs = r.closurePairs :=
    ((q.unpointedKey_eq_iff r).mp h).2.2
  rw [hC]

/-- If two complete pointed codes differ only in their CHOICE of
generating top vertex, those vertices belong to each other's complete
C-values. Consequently an unpointed key cannot enumerate them as
distinct closure-components. This does NOT yet build W. -/
theorem LiteralPointedCode.same_unpointed_generated_mutual
    (q r : LiteralPointedCode)
    (h : q.unpointedKey = r.unpointedKey)
    (hq : q.IsGeneratedByPoint)
    (hr : r.IsGeneratedByPoint) :
    q.point ∈ r.support ∧
    r.point ∈ q.support ∧
    (q.point,r.point) ∈ q.closurePairs ∧
    (r.point,q.point) ∈ q.closurePairs := by
  obtain ⟨hS,_,hC⟩ := (q.unpointedKey_eq_iff r).mp h
  have hQR : r.point ∈ q.support := by
    rw [hS]
    exact r.point_mem
  have hRQ : q.point ∈ r.support := by
    rw [← hS]
    exact q.point_mem
  have hFirst : (q.point,r.point) ∈ q.closurePairs :=
    (hq r.point).mp hQR
  have hSecond : (r.point,q.point) ∈ q.closurePairs := by
    rw [hC]
    exact (hr q.point).mp hRQ
  exact ⟨hRQ,hQR,hFirst,hSecond⟩

end FiniteUnaryCoordinates
end BigHrushovski
