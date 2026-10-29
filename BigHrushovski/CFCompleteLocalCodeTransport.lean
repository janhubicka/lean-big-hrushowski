import BigHrushovski.CFPartialSupportTuple
import BigHrushovski.FiniteGraphAdjacencyCodeTransport
import Mathlib.Data.Finset.Sort

/-!
# Complete ordered local C_F coordinates under named-support transport

A request's complete adjacency code is read in the order:
the increasing list of its *actual old support vertices*, followed
by the fresh ordinal interval. We prove that this coordinate list
commutes with an order isomorphism on the support and the fresh block.

Crucially, the support order isomorphism is obtained from a map
strictly increasing only on the selected finite old source. The
entire old stage need not embed into the target stage.

The generic full adjacency-matrix transport theorem then identifies
the complete ordered local codes, including old-old, old-new and
fresh-fresh edges and all corresponding nonedges.

This is still a conditional transport result: the target request
and its admissibility/size bound must be constructed separately.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [LinearOrder U] [DecidableEq U]
variable [LinearOrder V] [DecidableEq V]

/-- The literal image of a finite support under a map increasing
on the selected old source is order-isomorphic to the support.
No order-preserving map on the entire old stage is assumed. -/
noncomputable def supportOrderIsoOn
    (S P : Finset U) (f : U → V)
    (hf : StrictMonoOn f S) (hP : P ⊆ S)
    (Q : Finset V) (hQ : Q = P.image f) :
    SupportCarrier U P ≃o SupportCarrier V Q := by
  classical
  let g : SupportCarrier U P → SupportCarrier V Q :=
    fun p => ⟨f p.val, by
      rw [hQ]
      exact Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
  have hgMono : StrictMono g := by
    intro a b hab
    exact hf (hP a.property) (hP b.property) hab
  have hgSurj : Function.Surjective g := by
    intro q
    have hq : q.val ∈ P.image f := by
      rw [← hQ]
      exact q.property
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hq
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hfx
  exact OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono g hgMono) hgSurj

/-- An order isomorphism carries the sorted complete list of
one finite carrier to the sorted complete list of the other. -/
theorem sortedUniv_map_orderIso
    {P Q : Type*} [Fintype P] [LinearOrder P]
    [Fintype Q] [LinearOrder Q]
    (e : P ≃o Q) :
    ((Finset.univ : Finset P).sort (· ≤ ·)).map e =
      (Finset.univ : Finset Q).sort (· ≤ ·) := by
  classical
  let emb : P ↪ Q := e.toOrderEmbedding.toEmbedding
  have hMono : StrictMonoOn (emb : P → Q)
      (Finset.univ : Finset P) :=
    fun _ _ _ _ h => e.strictMono h
  have hSort := hMono.map_finsetSort
  have hUniv : (Finset.univ : Finset P).map emb =
      (Finset.univ : Finset Q) := by
    ext q
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      obtain ⟨p, rfl⟩ := e.surjective q
      exact Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩
  rw [hUniv] at hSort
  simpa [emb] using hSort

/-- The ordered local coordinates consist of all old coordinates
in increasing order, followed by all fresh coordinates in
increasing order. -/
noncomputable def sortedSumCoordinates
    (P B : Type*) [Fintype P] [LinearOrder P]
    [Fintype B] [LinearOrder B] : List (Sum P B) := by
  classical
  exact ((Finset.univ : Finset P).sort (· ≤ ·)).map Sum.inl ++
    ((Finset.univ : Finset B).sort (· ≤ ·)).map Sum.inr

/-- Both halves of the complete local coordinate list commute
with increasing relabelling. This includes empty supports. -/
theorem sortedSumCoordinates_map_orderIso
    {P Q B C : Type*}
    [Fintype P] [LinearOrder P]
    [Fintype Q] [LinearOrder Q]
    [Fintype B] [LinearOrder B]
    [Fintype C] [LinearOrder C]
    (e : P ≃o Q) (g : B ≃o C) :
    (sortedSumCoordinates P B).map (Sum.map e g) =
      sortedSumCoordinates Q C := by
  classical
  unfold sortedSumCoordinates
  rw [List.map_append]
  congr 1
  · calc
      (((Finset.univ : Finset P).sort (· ≤ ·)).map Sum.inl).map
          (Sum.map e g) =
        (((Finset.univ : Finset P).sort (· ≤ ·)).map e).map Sum.inl := by
          simp [List.map_map, Function.comp_def]
      _ = ((Finset.univ : Finset Q).sort (· ≤ ·)).map Sum.inl := by
        rw [sortedUniv_map_orderIso e]
  · calc
      (((Finset.univ : Finset B).sort (· ≤ ·)).map Sum.inr).map
          (Sum.map e g) =
        (((Finset.univ : Finset B).sort (· ≤ ·)).map g).map Sum.inr := by
          simp [List.map_map, Function.comp_def]
      _ = ((Finset.univ : Finset C).sort (· ≤ ·)).map Sum.inr := by
        rw [sortedUniv_map_orderIso g]

variable [Fintype U] [Fintype V]

/-- The actual request coordinate list is the generic ordered
old-plus-fresh list, without any renumbering. -/
theorem requestLocalCoordinates_eq_sortedSum
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    requestLocalCoordinates G Allowed bound r =
      sortedSumCoordinates (SupportCarrier U r.support)
        (Fin r.code.1.val) := by
  classical
  rfl

/-- Exact coordinate transport between two actual request records,
given increasing isomorphisms on their old support and fresh
ordinal intervals. -/
theorem requestLocalCoordinates_map_orderIso
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (e : SupportCarrier U r.support ≃o SupportCarrier V t.support)
    (g : Fin r.code.1.val ≃o Fin t.code.1.val) :
    (requestLocalCoordinates G AllowedU boundU r).map
        (Sum.map e g) =
      requestLocalCoordinates H AllowedV boundV t := by
  rw [requestLocalCoordinates_eq_sortedSum,
    requestLocalCoordinates_eq_sortedSum]
  exact sortedSumCoordinates_map_orderIso e g

/-- The full ordered adjacency code is invariant under an
induced isomorphism of the actual named support and fresh block.
The hypothesis reflects *all* adjacency, not just edges. -/
theorem requestAdjacencyCode_eq_of_localOrderIso
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (e : SupportCarrier U r.support ≃o SupportCarrier V t.support)
    (g : Fin r.code.1.val ≃o Fin t.code.1.val)
    (hAdj : ∀ x y : Sum (SupportCarrier U r.support)
        (Fin r.code.1.val),
      r.code.2.graph.adj x y ↔
        t.code.2.graph.adj (Sum.map e g x) (Sum.map e g y)) :
    requestAdjacencyCode G AllowedU boundU r =
      requestAdjacencyCode H AllowedV boundV t := by
  unfold requestAdjacencyCode
  exact GraphOn.orderedAdjacencyBits_of_coordinate_eq
    r.code.2.graph t.code.2.graph (Sum.map e g) hAdj
    (requestLocalCoordinates G AllowedU boundU r)
    (requestLocalCoordinates H AllowedV boundV t)
    (requestLocalCoordinates_map_orderIso G H AllowedU AllowedV
      boundU boundV r t e g).symm

end CFStageCatalogue
end BigHrushovski
