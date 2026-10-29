import BigHrushovski.CFActualNamedRequest
import BigHrushovski.CFExactOldFreshBoundary

/-!
# Complete old-fresh boundary under literal named-support transport

A simultaneous finite C_F level lift must preserve and reflect
edges from each selected old vertex u to every fresh vertex of
each source block. The source block's canonical support P lies
inside the selected old source S, and its image Q=f[P] is the
actual named target support.

We isolate the exact logical equivalence for one local code:
an old-fresh adjacency in the source occurs precisely when
there is a support vertex p=u adjacent to the fresh ordinal.
After relabelling by the prescribed support equivalence e:P≃Q,
the equivalent target statement has a vertex q=f[u] and the
corresponding edge of the transported local graph.

The map f need only be injective *on S*. The old source may
be a proper subset of the whole original stage, and the target
stage may be smaller. Edges and nonedges are treated symmetrically.

The lemma is generic for named-base graph transport. Connecting
it to the actual constructed StageRequest and tagged boundary
lemmas is the next step.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- Named-base graph transport fixes every fresh-fresh edge and
nonedge exactly, without any change to the finite ordinal. -/
theorem namedBaseGraph_fresh_iff
    (P : Finset U) (Q : Finset V)
    (e : SupportCarrier U P ≃ SupportCarrier V Q)
    (n : ℕ)
    (L : GraphOn (Sum (SupportCarrier U P) (Fin n)))
    (i j : Fin n) :
    (namedBaseGraph e L).adj (Sum.inr i) (Sum.inr j) ↔
      L.adj (Sum.inr i) (Sum.inr j) := by
  change L.adj (Sum.inr i) (Sum.inr j) ↔
    L.adj (Sum.inr i) (Sum.inr j)
  rfl

/-- The literal support membership condition and every
old-fresh adjacency are preserved and reflected under the
named-base pullback. No edge may arise to an old source
vertex outside the prescribed support P. -/
theorem namedBaseGraph_full_boundary_iff
    (P : Finset U) (Q : Finset V)
    (S : Finset U) (hP : P ⊆ S)
    (f : U → V) (hf : Set.InjOn f S)
    (e : SupportCarrier U P ≃ SupportCarrier V Q)
    (hVal : ∀ p : SupportCarrier U P,
      (e p).val = f p.val)
    (n : ℕ)
    (L : GraphOn (Sum (SupportCarrier U P) (Fin n)))
    (u : U) (hu : u ∈ S) (i : Fin n) :
    (∃ p : SupportCarrier U P,
      p.val = u ∧ L.adj (Sum.inl p) (Sum.inr i)) ↔
    (∃ q : SupportCarrier V Q,
      q.val = f u ∧
        (namedBaseGraph e L).adj (Sum.inl q) (Sum.inr i)) := by
  constructor
  · rintro ⟨p, hpu, hAdj⟩
    refine ⟨e p, ?_, ?_⟩
    · exact (hVal p).trans (congrArg f hpu)
    · apply (namedBaseGraph_adj_iff e L
        (Sum.inl (e p)) (Sum.inr i)).mpr
      simpa [namedBaseEquiv] using hAdj
  · rintro ⟨q, hqu, hAdj⟩
    let p : SupportCarrier U P := e.symm q
    have hp : e p = q := by simp [p]
    have hfu : f p.val = f u := by
      calc
        f p.val = (e p).val := (hVal p).symm
        _ = q.val := congrArg Subtype.val hp
        _ = f u := hqu
    have hpu : p.val = u := hf (hP p.property) hu hfu
    refine ⟨p, hpu, ?_⟩
    rw [← hp] at hAdj
    have hCode := (namedBaseGraph_adj_iff e L
      (Sum.inl (e p)) (Sum.inr i)).mp hAdj
    simpa [namedBaseEquiv] using hCode

end CFLocalCatalogue
end BigHrushovski
