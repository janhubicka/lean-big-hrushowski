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


/-- On a finite C-closed domain, equality of restricted complete
unary values is equivalent to equality of the entire ambient values.
This uses full image equality, not only preservation of membership. -/
theorem restrictValue_eq_iff_of_closed
    (C : V → Finset V) (s : Finset V)
    (hs : ClosedUnder C s) (u v : s) :
    restrictValue C s u = restrictValue C s v ↔
      C u.val = C v.val := by
  constructor
  · intro h
    have hImage := congrArg
      (fun t : Finset s => t.image (Subtype.val : s → V)) h
    simpa only [restrictValue_image C s hs u,
      restrictValue_image C s hs v] using hImage
  · intro h
    classical
    ext w
    rw [mem_restrictValue_iff C s u w,
      mem_restrictValue_iff C s v w, h]

/-- A vertex inside C(b) lies in its intrinsic lower part precisely
when its ambient COMPLETE unary value is not that of b. -/
theorem canonicalLocalLower_mem_iff_value_ne
    (G : GraphOn V) (κ : V → Fin n) (b : V)
    (u : FiniteC0.canonicalValue G κ b) :
    u ∈ canonicalLocalLower G κ b ↔
      FiniteC0.canonicalValue G κ u.val ≠
        FiniteC0.canonicalValue G κ b := by
  rw [mem_canonicalLocalLower_iff G κ b u]
  constructor
  · intro hu hEq
    exact (Finset.mem_sdiff.mp hu).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEq⟩)
  · intro hneq
    exact Finset.mem_sdiff.mpr ⟨u.property, by
      intro hc
      exact hneq (Finset.mem_filter.mp hc).2⟩

/-- The intrinsic lower part of the nested local C(b) is defined
without reference to an arbitrary chronological index: it consists
exactly of vertices whose COMPLETE unary values are different from
the value at b, as calculated inside the larger local C(a).
This is the lower-part compatibility needed in the hereditary
local-order catalogue. -/
theorem canonicalLocalInclusion_lower_iff
    (G : GraphOn V) (κ : V → Fin n)
    (a : V) (b : FiniteC0.canonicalValue G κ a)
    (u : FiniteC0.canonicalValue G κ b.val) :
    u ∈ canonicalLocalLower G κ b.val ↔
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a)
        (canonicalLocalInclusion G κ a b u) ≠
      restrictValue (FiniteC0.canonicalValue G κ)
        (FiniteC0.canonicalValue G κ a) b := by
  let C := FiniteC0.canonicalValue G κ
  have hClosed : ClosedUnder C (C a) :=
    FiniteC0.canonicalValue_oneGenerated_closed G κ a
  have hEq := restrictValue_eq_iff_of_closed C (C a) hClosed
    (canonicalLocalInclusion G κ a b u) b
  rw [canonicalLocalLower_mem_iff_value_ne G κ b.val u]
  constructor
  · intro hneq hRestricted
    exact hneq (hEq.mp hRestricted)
  · intro hneq hAmbient
    exact hneq (hEq.mpr hAmbient)

end FiniteUnaryCoordinates
end BigHrushovski
