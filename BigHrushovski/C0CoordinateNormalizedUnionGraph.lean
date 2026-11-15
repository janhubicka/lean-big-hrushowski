import BigHrushovski.C0CoordinateNormalizedAmalgamUnion
import BigHrushovski.C0CoordinateNormalizedFactorValues
import BigHrushovski.FiniteSetTaggedFreeGraph
import BigHrushovski.FiniteTaggedFreeGraphEquiv

/-!
# Exact graph on the normalized finite C₀ amalgam and literal closed union

The normalized two-sided C₀ amalgamation theorem gives its graph
on the tagged carrier obtained from the two finite factor inclusions.
For literal raw-host subsets S,T we identify the normalized tails
with the exclusive parts S\\T and T\\S. The generic free-graph
transport lemma identifies the resulting tagged graph with the
free graph of the two literal induced factors.

If S and T are closed under the complete raw unary function, their
exclusive parts have no crossing edges. Consequently the normalized
amalgam graph agrees with the raw graph induced on S∪T, including
every nonedge. This discharges the graph compatibility hypothesis
of the conditional finite two-sided stage/value theorem.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable [DecidableEq RawC0CoordinateVertex]

/-- The normalized left factor, after changing its abstract tail
to S\\T, has exactly the graph induced from the literal raw host.
The comparison is a full graph biconditional. -/
theorem RawC0CoordinateVertex.normalized_left_factor_graph
    (s t : Finset RawC0CoordinateVertex)
    (u v : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t)) :
    (FiniteSpan.normalGraph
      (rawC0HostGraph.pullback (Subtype.val : s → RawC0CoordinateVertex))
      (RawC0CoordinateVertex.overlapLeft s t)
      (RawC0CoordinateVertex.overlapLeft_injective s t)).adj u v ↔
    (rawC0HostGraph.pullback (FiniteSetUnion.leftVertex s t)).adj
      (FiniteSetUnion.factorTailEquiv
        (RawC0CoordinateVertex.overlapLeftTailEquiv s t) u)
      (FiniteSetUnion.factorTailEquiv
        (RawC0CoordinateVertex.overlapLeftTailEquiv s t) v) := by
  let i := RawC0CoordinateVertex.overlapLeft s t
  let hi := RawC0CoordinateVertex.overlapLeft_injective s t
  let l := RawC0CoordinateVertex.overlapLeftTailEquiv s t
  have hVertex (w : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail i) :
      ((FiniteSpan.splitEquiv i hi) w).val =
        FiniteSetUnion.leftVertex s t (FiniteSetUnion.factorTailEquiv l w) := by
    cases w with
    | inl p =>
        change ((FiniteSpan.splitEquiv i hi) (.inl p)).val = p.val
        rw [FiniteSpan.splitEquiv_inl]
        rfl
    | inr z =>
        change ((FiniteSpan.splitEquiv i hi) (.inr z)).val = z.val.val
        rw [FiniteSpan.splitEquiv_inr]
  change rawC0HostGraph.adj ((FiniteSpan.splitEquiv i hi u).val)
      ((FiniteSpan.splitEquiv i hi v).val) ↔
    rawC0HostGraph.adj
      (FiniteSetUnion.leftVertex s t (FiniteSetUnion.factorTailEquiv l u))
      (FiniteSetUnion.leftVertex s t (FiniteSetUnion.factorTailEquiv l v))
  rw [hVertex u, hVertex v]

/-- The corresponding complete graph equivalence for the right
normalized factor and its literal exclusive tail T\\S. -/
theorem RawC0CoordinateVertex.normalized_right_factor_graph
    (s t : Finset RawC0CoordinateVertex)
    (u v : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t)) :
    (FiniteSpan.normalGraph
      (rawC0HostGraph.pullback (Subtype.val : t → RawC0CoordinateVertex))
      (RawC0CoordinateVertex.overlapRight s t)
      (RawC0CoordinateVertex.overlapRight_injective s t)).adj u v ↔
    (rawC0HostGraph.pullback (FiniteSetUnion.rightVertex s t)).adj
      (FiniteSetUnion.factorTailEquiv
        (RawC0CoordinateVertex.overlapRightTailEquiv s t) u)
      (FiniteSetUnion.factorTailEquiv
        (RawC0CoordinateVertex.overlapRightTailEquiv s t) v) := by
  let j := RawC0CoordinateVertex.overlapRight s t
  let hj := RawC0CoordinateVertex.overlapRight_injective s t
  let r := RawC0CoordinateVertex.overlapRightTailEquiv s t
  have hVertex (w : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail j) :
      ((FiniteSpan.splitEquiv j hj) w).val =
        FiniteSetUnion.rightVertex s t (FiniteSetUnion.factorTailEquiv r w) := by
    cases w with
    | inl p =>
        change ((FiniteSpan.splitEquiv j hj) (.inl p)).val = p.val
        rw [FiniteSpan.splitEquiv_inl]
        rfl
    | inr z =>
        change ((FiniteSpan.splitEquiv j hj) (.inr z)).val = z.val.val
        rw [FiniteSpan.splitEquiv_inr]
  change rawC0HostGraph.adj ((FiniteSpan.splitEquiv j hj u).val)
      ((FiniteSpan.splitEquiv j hj v).val) ↔
    rawC0HostGraph.adj
      (FiniteSetUnion.rightVertex s t (FiniteSetUnion.factorTailEquiv r u))
      (FiniteSetUnion.rightVertex s t (FiniteSetUnion.factorTailEquiv r v))
  rw [hVertex u, hVertex v]

/-- The ACTUAL normalized two-sided finite C₀ free graph on the
literal factors S,T is exactly the raw-host graph induced on S∪T.
This includes negative adjacency incidences and does not require
choosing a preferred generator for any raw closure-component. -/
theorem RawC0CoordinateVertex.normalizedAmalgam_union_graph
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (x y : TaggedAmalgam.Carrier
      {q : RawC0CoordinateVertex // q ∈ s ∩ t}
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t))
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t))) :
    (TaggedAmalgam.freeGraph
      (FiniteSpan.normalGraph
        (rawC0HostGraph.pullback
          (Subtype.val : s → RawC0CoordinateVertex))
        (RawC0CoordinateVertex.overlapLeft s t)
        (RawC0CoordinateVertex.overlapLeft_injective s t))
      (FiniteSpan.normalGraph
        (rawC0HostGraph.pullback
          (Subtype.val : t → RawC0CoordinateVertex))
        (RawC0CoordinateVertex.overlapRight s t)
        (RawC0CoordinateVertex.overlapRight_injective s t))).adj x y ↔
    rawC0HostGraph.adj
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) x).val
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) y).val := by
  let l := RawC0CoordinateVertex.overlapLeftTailEquiv s t
  let r := RawC0CoordinateVertex.overlapRightTailEquiv s t
  have hVia := FiniteSetUnion.taggedFreeGraph_equiv_iff
    (FiniteSpan.normalGraph
      (rawC0HostGraph.pullback
        (Subtype.val : s → RawC0CoordinateVertex))
      (RawC0CoordinateVertex.overlapLeft s t)
      (RawC0CoordinateVertex.overlapLeft_injective s t))
    (FiniteSpan.normalGraph
      (rawC0HostGraph.pullback
        (Subtype.val : t → RawC0CoordinateVertex))
      (RawC0CoordinateVertex.overlapRight s t)
      (RawC0CoordinateVertex.overlapRight_injective s t))
    (rawC0HostGraph.pullback (FiniteSetUnion.leftVertex s t))
    (rawC0HostGraph.pullback (FiniteSetUnion.rightVertex s t))
    l r
    (fun u v => RawC0CoordinateVertex.normalized_left_factor_graph s t u v)
    (fun u v => RawC0CoordinateVertex.normalized_right_factor_graph s t u v)
    x y
  have hLiteral :=
    rawC0TaggedFreeGraph_adj_iff s t hs ht
      (FiniteSetUnion.taggedTailsEquiv l r x)
      (FiniteSetUnion.taggedTailsEquiv l r y)
  have hTransport := hVia.trans hLiteral
  change (TaggedAmalgam.freeGraph
      (FiniteSpan.normalGraph
        (rawC0HostGraph.pullback (Subtype.val : s → RawC0CoordinateVertex))
        (RawC0CoordinateVertex.overlapLeft s t)
        (RawC0CoordinateVertex.overlapLeft_injective s t))
      (FiniteSpan.normalGraph
        (rawC0HostGraph.pullback (Subtype.val : t → RawC0CoordinateVertex))
        (RawC0CoordinateVertex.overlapRight s t)
        (RawC0CoordinateVertex.overlapRight_injective s t))).adj x y ↔
    rawC0HostGraph.adj
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) x).val
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) y).val at hTransport
  exact hTransport

end FiniteUnaryCoordinates
end BigHrushovski
