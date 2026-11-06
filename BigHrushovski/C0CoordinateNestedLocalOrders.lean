import BigHrushovski.C0CoordinateCanonicalLocalRepresentative

/-!
# Nested one-generated C₀ ordered closures

Every vertex b inside the one-generated closure C(a) has its own
one-generated closure C(b) included in C(a). The literal subtype
inclusion preserves the inherited order, both edges and nonedges,
and the COMPLETE unary C and J values.

This is the finite comparison between actual occurrences needed by
the hereditary local-order catalogue. It is weaker than asserting
that independently CHOSEN ordered representatives agree: such
agreement remains a separate recursive choice condition.

The argument uses actual finite canonical C₀ values and does not
assume a countable generic limit or construct the host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
variable {n : ℕ}

/-- If b is inside C(a), then C(b) is a literal finite subset of
C(a). No arbitrary renumbering is introduced. -/
def canonicalLocalInclusion
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a) :
    FiniteC0.canonicalValue G κ b.val →
      FiniteC0.canonicalValue G κ a :=
  fun u => ⟨u.val,
    FiniteC0.canonicalValue_mem_trans G κ b.property u.property⟩

theorem canonicalLocalInclusion_injective
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a) :
    Function.Injective (canonicalLocalInclusion G κ a b) := by
  intro u v h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- The nested inclusion preserves and reflects the complete
inherited linear order. -/
theorem canonicalLocalInclusion_lt_iff
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (u v : FiniteC0.canonicalValue G κ b.val) :
    canonicalLocalInclusion G κ a b u <
      canonicalLocalInclusion G κ a b v ↔ u < v :=
  Iff.rfl

/-- Both edges and nonedges agree in the two induced finite graphs.
This is inducedness, not merely edge preservation. -/
theorem canonicalLocalInclusion_adj_iff
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (u v : FiniteC0.canonicalValue G κ b.val) :
    (restrictGraph G (FiniteC0.canonicalValue G κ b.val)).adj u v ↔
      (restrictGraph G (FiniteC0.canonicalValue G κ a)).adj
        (canonicalLocalInclusion G κ a b u)
        (canonicalLocalInclusion G κ a b v) :=
  Iff.rfl

/-- The complete unary value of every nested vertex is transported
by the literal inclusion as an EQUALITY of finite sets. -/
theorem canonicalLocalInclusion_C_image
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (u : FiniteC0.canonicalValue G κ b.val) :
    ((restrictValue (FiniteC0.canonicalValue G κ)
      (FiniteC0.canonicalValue G κ b.val) u).image
        (canonicalLocalInclusion G κ a b)) =
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a)
        (canonicalLocalInclusion G κ a b u) := by
  let C := FiniteC0.canonicalValue G κ
  have hSubset : C b.val ⊆ C a :=
    fun _ h => FiniteC0.canonicalValue_mem_trans G κ b.property h
  have hClosed : ClosedUnder C (C b.val) :=
    FiniteC0.canonicalValue_oneGenerated_closed G κ b.val
  exact restrictValue_restrict C (C a) (C b.val) hSubset hClosed u

/-- The graph-derived complete J-value is likewise preserved by
nested inclusion; this is the operation used in the coordinate host.
It relies on full C-closedness, not only induced graph adjacency. -/
theorem canonicalLocalInclusion_J_image
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (u : FiniteC0.canonicalValue G κ b.val) :
    (((restrictGraph G (FiniteC0.canonicalValue G κ b.val)).
        backAdjacencyValue
          (restrictValue (FiniteC0.canonicalValue G κ)
            (FiniteC0.canonicalValue G κ b.val)) u).image
        (canonicalLocalInclusion G κ a b)) =
      (restrictGraph G (FiniteC0.canonicalValue G κ a)).
        backAdjacencyValue
          (restrictValue (FiniteC0.canonicalValue G κ)
            (FiniteC0.canonicalValue G κ a))
          (canonicalLocalInclusion G κ a b u) := by
  let C := FiniteC0.canonicalValue G κ
  have hSubset : C b.val ⊆ C a :=
    fun _ h => FiniteC0.canonicalValue_mem_trans G κ b.property h
  have hClosed : ClosedUnder C (C b.val) :=
    FiniteC0.canonicalValue_oneGenerated_closed G κ b.val
  rw [restrictBackAdjacencyValue G C (C b.val) u,
    restrictBackAdjacencyValue G C (C a)
      (canonicalLocalInclusion G κ a b u)]
  exact restrictBackAdjacencyValue_restrict G C
    (C a) (C b.val) hSubset hClosed u

end FiniteUnaryCoordinates
end BigHrushovski
