import BigHrushovski.CFNamedBaseTransport
import BigHrushovski.CFOrderedNormalization

/-!
# Complete old-fresh boundary after relabelling the canonical C_F support

An arbitrary finite desired graph may have a large old part V
and a fresh ordered block B. Its canonical old support is a
finite subset P of V. Restrict the desired graph to P ⊕ B,
relabel P by an actual induced support equivalence P ≃ Q,
and enumerate B increasingly by Fin(card B).

The normalized local graph over the literal target support Q
retains the complete boundary relation. If the original fresh
vertices have no old neighbours outside P, then every
old--fresh edge of the desired graph is *equivalent* to the
corresponding normalized local edge over a support vertex of Q.
This includes the reflection of all nonedges.

The result bridges the canonical finite local-support theorem
with the exact tagged old--fresh boundary certificate. It does
not assert that Q is d-closed or that the local graph is an
admissible growth-class code; those are separate established
inputs to the complete one-block response.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {V U B : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype U] [DecidableEq U]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- Complete local graph on a literal old subtype P and
the original finite ordered fresh block B. -/
noncomputable def oldSubsetLocalGraph
    (H : GraphOn (Sum V B)) (P : Finset V) :
    GraphOn (Sum {v : V // v ∈ P} B) :=
  H.pullback (fun
    | Sum.inl p => Sum.inl p.val
    | Sum.inr b => Sum.inr b)

/-- Relabel the literal old subtype to Q and the new block
increasingly. Neither the fresh order nor any edge is lost. -/
noncomputable def transportedLocalGraph
    (H : GraphOn (Sum V B)) (P : Finset V)
    {Q : Finset U} (e : {v : V // v ∈ P} ≃ {u : U // u ∈ Q}) :
    GraphOn (Sum {u : U // u ∈ Q} (Fin (Fintype.card B))) :=
  orderedNormalizeGraph
    (namedBaseGraph e (oldSubsetLocalGraph H P))

/-- The increasing transport preserves every fresh--fresh
edge and every corresponding nonedge. -/
theorem transportedLocal_fresh_iff
    (H : GraphOn (Sum V B)) (P : Finset V)
    {Q : Finset U} (e : {v : V // v ∈ P} ≃ {u : U // u ∈ Q})
    (i j : Fin (Fintype.card B)) :
    (transportedLocalGraph H P e).adj (Sum.inr i) (Sum.inr j) ↔
      H.adj
        (Sum.inr (increasingNewBlock (B := B) i))
        (Sum.inr (increasingNewBlock (B := B) j)) := by
  simp [transportedLocalGraph, oldSubsetLocalGraph,
    orderedNormalizeGraph, namedBaseGraph,
    taggedIncreasingEquiv, namedBaseEquiv, GraphOn.pullback]

/-- At the actual named vertex e(p) of Q, the normalized
old--fresh adjacency is exactly the original adjacency
of p to the increasing fresh vertex. -/
theorem transportedLocal_support_boundary_iff
    (H : GraphOn (Sum V B)) (P : Finset V)
    {Q : Finset U} (e : {v : V // v ∈ P} ≃ {u : U // u ∈ Q})
    (p : {v : V // v ∈ P}) (i : Fin (Fintype.card B)) :
    (transportedLocalGraph H P e).adj
      (Sum.inl (e p)) (Sum.inr i) ↔
      H.adj (Sum.inl p.val)
        (Sum.inr (increasingNewBlock (B := B) i)) := by
  simp [transportedLocalGraph, oldSubsetLocalGraph,
    orderedNormalizeGraph, namedBaseGraph,
    taggedIncreasingEquiv, namedBaseEquiv, GraphOn.pullback]

/-- Full boundary matching for the entire old source V.
All new neighbours must lie in the canonical source support P,
and the embedded support equivalence names them literally
in the target Q. -/
theorem transportedLocal_full_boundary_iff
    (H : GraphOn (Sum V B)) (P : Finset V)
    (Q : Finset U)
    (f : V → U) (hf : Function.Injective f)
    (e : {v : V // v ∈ P} ≃ {u : U // u ∈ Q})
    (hVal : ∀ p : {v : V // v ∈ P}, (e p).val = f p.val)
    (hBack : ∀ x : V, ∀ b : B,
      H.adj (Sum.inl x) (Sum.inr b) → x ∈ P)
    (x : V) (i : Fin (Fintype.card B)) :
    H.adj (Sum.inl x)
      (Sum.inr (increasingNewBlock (B := B) i)) ↔
      ∃ q : {u : U // u ∈ Q},
        q.val = f x ∧
        (transportedLocalGraph H P e).adj
          (Sum.inl q) (Sum.inr i) := by
  constructor
  · intro h
    let p : {v : V // v ∈ P} :=
      ⟨x, hBack x (increasingNewBlock (B := B) i) h⟩
    refine ⟨e p, hVal p, ?_⟩
    exact (transportedLocal_support_boundary_iff H P e p i).mpr h
  · rintro ⟨q, hq, hCode⟩
    let p : {v : V // v ∈ P} := e.symm q
    have hP : e p = q := by simp [p]
    rw [← hP] at hCode
    have hOriginal :
        H.adj (Sum.inl p.val)
          (Sum.inr (increasingNewBlock (B := B) i)) :=
      (transportedLocal_support_boundary_iff H P e p i).mp hCode
    have hEq : p.val = x := by
      apply hf
      calc
        f p.val = (e p).val := (hVal p).symm
        _ = q.val := congrArg Subtype.val hP
        _ = f x := hq
    simpa only [hEq] using hOriginal

end CFLocalCatalogue
end BigHrushovski
