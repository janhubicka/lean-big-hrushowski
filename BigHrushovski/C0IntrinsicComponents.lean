import BigHrushovski.C0FinitePrefixPersistence

/-!
# Canonical C0 components are intrinsic to the named unary function

In a canonical finite C0 presentation, two vertices have the same
complete unary value if and only if they belong to the same
minimal-strong component. The forward implication follows because
each value contains its own complete component while all backward
dependency paths strictly decrease component indices.

Thus the partition into closure-components is determined by the
finite set-valued unary function, even though the particular
linear order of those components is not. Two presentations
defining the same unary function have the same component
partition, up to chronological relabelling.

These lemmas are a useful first interface for proving free
amalgamation of *two* finite functional C0 structures over a common
closed base, whose witness component orders need not agree.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- A vertex belongs to its own complete canonical unary closure. -/
theorem mem_canonicalValue_self
    (G : GraphOn V) (κ : V → Fin n) (u : V) :
    u ∈ canonicalValue G κ u := by
  exact (mem_canonicalValue_iff G κ u u).mpr
    TaggedAmalgam.DependencyAncestor.root

/-- Two vertices have equal full set-valued unary values precisely
when their component indices agree. The component order need not
be specified, and nonempty component fibres may have arbitrary size. -/
theorem canonicalValue_eq_iff_index_eq
    (G : GraphOn V) (κ : V → Fin n) (u v : V) :
    canonicalValue G κ u = canonicalValue G κ v ↔
      κ u = κ v := by
  constructor
  · intro hEq
    have huV : u ∈ canonicalValue G κ v := by
      rw [← hEq]
      exact mem_canonicalValue_self G κ u
    have hvU : v ∈ canonicalValue G κ u := by
      rw [hEq]
      exact mem_canonicalValue_self G κ v
    have hUV : (κ u).val ≤ (κ v).val :=
      canonicalAncestor_index_le G κ
        ((mem_canonicalValue_iff G κ v u).mp huV)
    have hVU : (κ v).val ≤ (κ u).val :=
      canonicalAncestor_index_le G κ
        ((mem_canonicalValue_iff G κ u v).mp hvU)
    exact Fin.ext (le_antisymm hUV hVU)
  · intro hIndex
    ext w
    simp only [mem_canonicalValue_iff]
    rw [hIndex]

/-- The complete vertex set of the component of u is recovered
solely by equality with its set-valued unary function value. -/
theorem component_eq_unary_value_class
    (G : GraphOn V) (κ : V → Fin n) (u : V) :
    component κ (κ u).val =
      Finset.univ.filter (fun v => canonicalValue G κ v =
        canonicalValue G κ u) := by
  classical
  ext v
  simp only [mem_component_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    have hIndex : κ v = κ u := Fin.ext hv
    exact (canonicalValue_eq_iff_index_eq G κ v u).mpr hIndex
  · intro hv
    exact congrArg Fin.val
      ((canonicalValue_eq_iff_index_eq G κ v u).mp hv)

/-- Two finite canonical presentations with the same actual unary
function, possibly indexed by different finite ordinal types,
partition the vertex set into exactly the same components. -/
theorem same_components_of_equal_canonicalValues
    {m : ℕ}
    (G : GraphOn V) (κ : V → Fin n) (λ : V → Fin m)
    (hValues : ∀ u : V,
      canonicalValue G κ u = canonicalValue G λ u)
    (u v : V) :
    (κ u = κ v) ↔ (λ u = λ v) := by
  constructor
  · intro hκ
    have heqOld :=
      (canonicalValue_eq_iff_index_eq G κ u v).mpr hκ
    have heqNew : canonicalValue G λ u = canonicalValue G λ v :=
      (hValues u).symm.trans (heqOld.trans (hValues v))
    exact (canonicalValue_eq_iff_index_eq G λ u v).mp heqNew
  · intro hλ
    have heqNew :=
      (canonicalValue_eq_iff_index_eq G λ u v).mpr hλ
    have heqOld : canonicalValue G κ u = canonicalValue G κ v :=
      (hValues u).trans (heqNew.trans (hValues v).symm)
    exact (canonicalValue_eq_iff_index_eq G κ u v).mp heqOld

end FiniteC0
end BigHrushovski
