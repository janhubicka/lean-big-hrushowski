import BigHrushovski.TaggedAmalgam

/-!
# The literal union of two finite sets as a tagged common base and tails

The finite C₀ functional amalgam is constructed on a tagged carrier
consisting of a common base and two disjoint tails. When both factors
are literal subsets of the SAME host, this carrier is canonically
equivalent to their literal union.

The equivalence below applies to arbitrary finite subsets of any
type; it does not depend on a graph, predimension, component order,
or choice of representative. In later Track D arguments it will be
used to transport the finite functional amalgam to an actual finite
C-closed union of raw coordinate-host vertices.

No finite-age, graph or Ramsey conclusion is inferred here.
-/

namespace BigHrushovski
namespace FiniteSetUnion

variable {V : Type*} [DecidableEq V]

/-- The literal common part and the two exclusive parts. -/
abbrev Common (s t : Finset V) : Type* :=
  {v : V // v ∈ s ∩ t}

abbrev LeftOnly (s t : Finset V) : Type* :=
  {v : V // v ∈ s ∧ v ∉ t}

abbrev RightOnly (s t : Finset V) : Type* :=
  {v : V // v ∈ t ∧ v ∉ s}

/-- Three-tag carrier with one copy of the overlap and one copy of
each exclusive part, retaining the original underlying vertex. -/
abbrev TaggedCarrier (s t : Finset V) : Type* :=
  TaggedAmalgam.Carrier (Common s t) (LeftOnly s t) (RightOnly s t)

/-- Forget the disjoint tags but retain the full literal union
element. No identification other than the common base is made. -/
def taggedUnionMap (s t : Finset V) :
    TaggedCarrier s t → {v : V // v ∈ s ∪ t}
  | .inl p =>
      ⟨p.val, Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mp p.property).1)⟩
  | .inr (.inl x) =>
      ⟨x.val, Finset.mem_union.mpr (Or.inl x.property.1)⟩
  | .inr (.inr x) =>
      ⟨x.val, Finset.mem_union.mpr (Or.inr x.property.1)⟩

/-- Different tags cannot represent the same literal union vertex.
The contradiction in each cross-tag case uses membership in the
common base versus exclusion from the corresponding tail. -/
theorem taggedUnionMap_injective (s t : Finset V) :
    Function.Injective (taggedUnionMap s t) := by
  intro x y h
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          have hv : p.val = q.val := congrArg Subtype.val h
          exact congrArg Sum.inl (Subtype.ext hv)
      | inr y =>
          cases y with
          | inl q =>
              have hv : p.val = q.val := congrArg Subtype.val h
              have hpT : p.val ∈ t := (Finset.mem_inter.mp p.property).2
              exact False.elim (q.property.2 (hv ▸ hpT))
          | inr q =>
              have hv : p.val = q.val := congrArg Subtype.val h
              have hpS : p.val ∈ s := (Finset.mem_inter.mp p.property).1
              exact False.elim (q.property.2 (hv ▸ hpS))
  | inr x =>
      cases x with
      | inl p =>
          cases y with
          | inl q =>
              have hv : p.val = q.val := congrArg Subtype.val h
              have hqT : q.val ∈ t := (Finset.mem_inter.mp q.property).2
              exact False.elim (p.property.2 (hv.symm ▸ hqT))
          | inr y =>
              cases y with
              | inl q =>
                  have hv : p.val = q.val := congrArg Subtype.val h
                  exact congrArg (fun z => Sum.inr (Sum.inl z))
                    (Subtype.ext hv)
              | inr q =>
                  have hv : p.val = q.val := congrArg Subtype.val h
                  exact False.elim (q.property.2 (hv ▸ p.property.1))
      | inr p =>
          cases y with
          | inl q =>
              have hv : p.val = q.val := congrArg Subtype.val h
              have hqS : q.val ∈ s := (Finset.mem_inter.mp q.property).1
              exact False.elim (p.property.2 (hv.symm ▸ hqS))
          | inr y =>
              cases y with
              | inl q =>
                  have hv : p.val = q.val := congrArg Subtype.val h
                  exact False.elim (p.property.2 (hv.symm ▸ q.property.1))
              | inr q =>
                  have hv : p.val = q.val := congrArg Subtype.val h
                  exact congrArg (fun z => Sum.inr (Sum.inr z))
                    (Subtype.ext hv)

/-- Every literal union vertex is either in the common base or
in exactly one of the two tails. -/
theorem taggedUnionMap_surjective (s t : Finset V) :
    Function.Surjective (taggedUnionMap s t) := by
  intro v
  rcases Finset.mem_union.mp v.property with hs | ht
  · by_cases hvt : v.val ∈ t
    · refine ⟨Sum.inl ⟨v.val,Finset.mem_inter.mpr ⟨hs,hvt⟩⟩,?_⟩
      exact Subtype.ext rfl
    · refine ⟨Sum.inr (Sum.inl ⟨v.val,hs,hvt⟩),?_⟩
      exact Subtype.ext rfl
  · by_cases hvs : v.val ∈ s
    · refine ⟨Sum.inl ⟨v.val,Finset.mem_inter.mpr ⟨hvs,ht⟩⟩,?_⟩
      exact Subtype.ext rfl
    · refine ⟨Sum.inr (Sum.inr ⟨v.val,ht,hvs⟩),?_⟩
      exact Subtype.ext rfl

/-- Exact finite carrier equivalence between the tagged common
base/tails and the literal union. This is the set-theoretic
transport needed for a two-sided finite functional amalgam. -/
noncomputable def taggedUnionEquiv (s t : Finset V) :
    TaggedCarrier s t ≃ {v : V // v ∈ s ∪ t} :=
  Equiv.ofBijective (taggedUnionMap s t)
    ⟨taggedUnionMap_injective s t,
      taggedUnionMap_surjective s t⟩

end FiniteSetUnion
end BigHrushovski
