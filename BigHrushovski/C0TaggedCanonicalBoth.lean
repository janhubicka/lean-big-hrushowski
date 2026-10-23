import BigHrushovski.C0TaggedClosedFactors

/-!
# Both actual canonical unary closures in a tagged finite C0 free graph

Take two component-indexed finite C0 graph presentations sharing a
named closed base. The left chronology is unchanged. The right base
is frontloaded and the fresh right components follow all left ones.

The input compatibility conditions are ONLY:
* induced agreement of the two graphs on the named base;
* equality of the component partitions on the common base;
* orientation agreement for edges between those base components;
* right-base frontloading before the right tail;
* closedness of the common base under the left canonical unary function.

These conditions concern the ORIGINAL factors and their named base,
and are verified separately from shared unary values in the
finite C0 presentation. No equality of the desired joined unary
function is presumed.

The theorem below proves simultaneous equality of every vertex in
the complete canonical unary function of both factors inside the
ACTUAL tagged graph freeGraph G H, with the ACTUAL joined Fin-valued
component index.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- Main concrete two-sided finite C0 unary-value preservation theorem. -/
theorem taggedCanonicalValues_both
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hBaseComponents : ∀ p q : P,
      κL (.inl p) = κL (.inl q) ↔
      κR (.inl p) = κR (.inl q))
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (hBaseOrient : ∀ p q : P,
      H.adj (.inl p) (.inl q) →
      ((κL (.inl p)).val < (κL (.inl q)).val ↔
       (κR (.inl p)).val < (κR (.inl q)).val))
    (hBaseClosed : G.IsClosedUnderValues
      (FiniteC0.canonicalValue G κL)
      ((Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L))) :
    (∀ u : Sum P L,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (leftTag u) =
      (FiniteC0.canonicalValue G κL u).image
        (leftTag : Sum P L → Carrier P L R)) ∧
    (∀ u : Sum P R,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (rightTag u) =
      (FiniteC0.canonicalValue H κR u).image
        (rightTag : Sum P R → Carrier P L R)) := by
  constructor
  · intro u
    apply FiniteC0.canonicalValue_transport_of_closed_embedding
      G (freeGraph G H) κL (joinedIndex κL κR)
      (leftTag : Sum P L → Carrier P L R)
    · intro x y
      exact (freeGraph_left G H hAgree x y).symm
    · intro x y
      exact joinedIndex_left_component_iff κL κR x y
    · intro x y _
      exact joinedIndex_left_edge_orientation κL κR x y
    · exact leftTaggedImage_closed G H κL κR
  · intro u
    apply FiniteC0.canonicalValue_transport_of_closed_embedding
      H (freeGraph G H) κR (joinedIndex κL κR)
      (rightTag : Sum P R → Carrier P L R)
    · intro x y
      exact (freeGraph_right G H hAgree x y).symm
    · intro x y
      exact joinedIndex_right_component_iff κL κR
        hBaseComponents hFront x y
    · intro x y hEdge
      exact joinedIndex_right_edge_orientation
        H κL κR hFront hBaseOrient x y hEdge
    · exact rightTaggedImage_closed
        G H hAgree κL κR hBaseClosed

end TaggedAmalgam
end BigHrushovski
