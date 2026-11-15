import BigHrushovski.FiniteSetTaggedUnion
import BigHrushovski.C0CoordinateRawHostFiniteClosure

/-!
# A tagged finite free graph is exactly the literal induced union

The tagged carrier of finite subsets S,T consists of their common
base, left-exclusive vertices, and right-exclusive vertices.
If the ambient graph has no crossing edges between the two exclusive
parts, the free graph of its two induced factors is EXACTLY the graph
induced on S∪T under the tagged-carrier equivalence.

The argument is purely graph-theoretic and applies to any graph:
the seven same-factor cases use the existing tagged-free-graph
embedding lemmas, and the two cross-tail cases use no-cross edges.

This is a reusable part of the finite functional C₀ and C_F
amalgamation constructions. It preserves nonedges as well as edges.
Complete unary C-values and canonical component stages are separate.
-/

namespace BigHrushovski
namespace FiniteSetUnion

variable {V : Type*} [DecidableEq V]

/-- Literal vertex of the left factor, both in the common base
and in the left-exclusive part. -/
def leftVertex (s t : Finset V) :
    Common s t ⊕ LeftOnly s t → V
  | .inl p => p.val
  | .inr x => x.val

/-- Literal vertex of the right factor. -/
def rightVertex (s t : Finset V) :
    Common s t ⊕ RightOnly s t → V
  | .inl p => p.val
  | .inr x => x.val

/-- A free tagged graph formed from the two literal induced factors.
The common base is represented once and no cross-tail edges are added. -/
def taggedFreeGraph (G : GraphOn V) (s t : Finset V) :
    GraphOn (TaggedCarrier s t) :=
  TaggedAmalgam.freeGraph
    (G.pullback (leftVertex s t))
    (G.pullback (rightVertex s t))

/-- The tagged free graph preserves and reflects EVERY graph pair
in the literal union, assuming only that no edge joins the two
exclusive parts. Unlike an embedding theorem in one direction,
this also reflects all NONEDGES between the factors. -/
theorem taggedFreeGraph_adj_iff
    (G : GraphOn V) (s t : Finset V)
    (hNoCross : ∀ u : V, u ∈ s → u ∉ t →
      ∀ v : V, v ∈ t → v ∉ s → ¬ G.adj u v)
    (x y : TaggedCarrier s t) :
    (taggedFreeGraph G s t).adj x y ↔
      G.adj (taggedUnionMap s t x).val
        (taggedUnionMap s t y).val := by
  let L := G.pullback (leftVertex s t)
  let R := G.pullback (rightVertex s t)
  have hAgree : TaggedAmalgam.AgreeBase L R := by
    intro p q
    exact Iff.rfl
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          change (TaggedAmalgam.freeGraph L R).adj
            (TaggedAmalgam.leftTag (.inl p))
            (TaggedAmalgam.leftTag (.inl q)) ↔
            L.adj (.inl p) (.inl q)
          exact TaggedAmalgam.freeGraph_left L R hAgree (.inl p) (.inl q)
      | inr y =>
          cases y with
          | inl l =>
              change (TaggedAmalgam.freeGraph L R).adj
                (TaggedAmalgam.leftTag (.inl p))
                (TaggedAmalgam.leftTag (.inr l)) ↔
                L.adj (.inl p) (.inr l)
              exact TaggedAmalgam.freeGraph_left L R hAgree (.inl p) (.inr l)
          | inr r =>
              change (TaggedAmalgam.freeGraph L R).adj
                (TaggedAmalgam.rightTag (.inl p))
                (TaggedAmalgam.rightTag (.inr r)) ↔
                R.adj (.inl p) (.inr r)
              exact TaggedAmalgam.freeGraph_right L R hAgree (.inl p) (.inr r)
  | inr x =>
      cases x with
      | inl l =>
          cases y with
          | inl p =>
              change (TaggedAmalgam.freeGraph L R).adj
                (TaggedAmalgam.leftTag (.inr l))
                (TaggedAmalgam.leftTag (.inl p)) ↔
                L.adj (.inr l) (.inl p)
              exact TaggedAmalgam.freeGraph_left L R hAgree (.inr l) (.inl p)
          | inr y =>
              cases y with
              | inl m =>
                  change (TaggedAmalgam.freeGraph L R).adj
                    (TaggedAmalgam.leftTag (.inr l))
                    (TaggedAmalgam.leftTag (.inr m)) ↔
                    L.adj (.inr l) (.inr m)
                  exact TaggedAmalgam.freeGraph_left L R hAgree (.inr l) (.inr m)
              | inr r =>
                  change (TaggedAmalgam.freeGraph L R).adj
                    (.inr (.inl l)) (.inr (.inr r)) ↔
                      G.adj l.val r.val
                  constructor
                  · intro h
                    exact False.elim
                      (TaggedAmalgam.freeGraph_no_cross L R l r h)
                  · intro h
                    exact False.elim
                      (hNoCross l.val l.property.1 l.property.2
                        r.val r.property.1 r.property.2 h)
      | inr r =>
          cases y with
          | inl p =>
              change (TaggedAmalgam.freeGraph L R).adj
                (TaggedAmalgam.rightTag (.inr r))
                (TaggedAmalgam.rightTag (.inl p)) ↔
                R.adj (.inr r) (.inl p)
              exact TaggedAmalgam.freeGraph_right L R hAgree (.inr r) (.inl p)
          | inr y =>
              cases y with
              | inl l =>
                  change (TaggedAmalgam.freeGraph L R).adj
                    (.inr (.inr r)) (.inr (.inl l)) ↔
                      G.adj r.val l.val
                  constructor
                  · intro h
                    have h' : (TaggedAmalgam.freeGraph L R).adj
                        (.inr (.inl l)) (.inr (.inr r)) :=
                      (TaggedAmalgam.freeGraph L R).symm _ _ h
                    exact False.elim
                      (TaggedAmalgam.freeGraph_no_cross L R l r h')
                  · intro h
                    have h' : G.adj l.val r.val := G.symm _ _ h
                    exact False.elim
                      (hNoCross l.val l.property.1 l.property.2
                        r.val r.property.1 r.property.2 h')
              | inr m =>
                  change (TaggedAmalgam.freeGraph L R).adj
                    (TaggedAmalgam.rightTag (.inr r))
                    (TaggedAmalgam.rightTag (.inr m)) ↔
                    R.adj (.inr r) (.inr m)
                  exact TaggedAmalgam.freeGraph_right L R hAgree (.inr r) (.inr m)

end FiniteSetUnion

namespace FiniteUnaryCoordinates

variable [DecidableEq RawC0CoordinateVertex]

/-- The tagged free graph of two literal C-closed raw-host factors
is exactly their induced graph on the union. No-cross edges follow
from the already verified complete unary closure calculus. -/
theorem rawC0TaggedFreeGraph_adj_iff
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (x y : FiniteSetUnion.TaggedCarrier s t) :
    (FiniteSetUnion.taggedFreeGraph rawC0HostGraph s t).adj x y ↔
      rawC0HostGraph.adj
        (FiniteSetUnion.taggedUnionMap s t x).val
        (FiniteSetUnion.taggedUnionMap s t y).val := by
  apply FiniteSetUnion.taggedFreeGraph_adj_iff
    rawC0HostGraph s t
  intro u huS huT v hvT hvS
  exact rawC0HostGraph_noCross_between s t hs ht
    huS huT hvT hvS

end FiniteUnaryCoordinates
end BigHrushovski
