import BigHrushovski.C0StrongAge

/-!
# Strong extensions with a genuinely fresh vertex

For a countable strong Fraïssé construction, local responses to
extension requests are insufficient: successive finite stages must
also exhaust the chosen countable carrier.

We show that every finite two-sparse graph has a finite two-sparse
strong extension containing at least one vertex outside the old
strong image. We realize it by strongly amalgamating with a one-vertex
edgeless graph over the empty strong substructure. The tagged finite
free amalgam avoids all accidental vertex identifications.

This is a finite growth lemma, not a countable Fraïssé construction.
-/

namespace BigHrushovski

namespace GraphOn

/-- The unique graph on a singleton, with no edges. -/
def onePointGraph : GraphOn Unit where
  adj _ _ := False
  symm := by
    intro _ _ h
    exact False.elim h
  irrefl := by
    intro _ h
    exact h

/-- Every subset of the one-point graph has nonnegative predimension. -/
theorem onePointGraph_sparse :
    onePointGraph.IsTwoSparse (Finset.univ : Finset Unit) := by
  classical
  intro s _
  have hEdges : onePointGraph.edgesWithin s = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    have heEdge : onePointGraph.IsEdge e :=
      (onePointGraph.mem_edgesWithin_iff s e).mp he |>.2
    obtain ⟨x, _, y, _, hxy⟩ := heEdge.2
    exact hxy
  simp [predim, hEdges]

end GraphOn

namespace FiniteSpan

/-- In every finite two-sparse graph, one can add at least one genuinely
fresh vertex while keeping the old graph as an induced strong subgraph
of a finite two-sparse graph. The fresh vertex is distinct from all
old labelled vertices, even when the input type is empty. -/
theorem exists_fresh_strong_extension
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : GraphOn V)
    (hSparse : G.IsTwoSparse (Finset.univ : Finset V)) :
    ∃ (K : GraphOn (JointCarrier V Unit))
      (old : V → JointCarrier V Unit)
      (fresh : JointCarrier V Unit),
      Function.Injective old ∧
      (∀ x y : V, K.adj (old x) (old y) ↔ G.adj x y) ∧
      K.IsTwoSparse Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset V).image old) Finset.univ ∧
      fresh ∉ (Finset.univ : Finset V).image old := by
  classical
  let i : Empty → V := Empty.elim
  let j : Empty → Unit := Empty.elim
  have hi : Function.Injective i := fun p _ _ => Empty.elim p
  have hj : Function.Injective j := fun p _ _ => Empty.elim p
  have hAgree : ∀ p q : Empty,
      G.adj (i p) (i q) ↔ GraphOn.onePointGraph.adj (j p) (j q) := by
    intro p
    exact Empty.elim p
  have hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset Empty).image i)
      (Finset.univ : Finset V) := by
    have hEmpty : ((Finset.univ : Finset Empty).image i) =
        (∅ : Finset V) := by
      simp
    rw [hEmpty]
    exact G.empty_strong_of_twoSparse hSparse
  have hStrongOne : GraphOn.onePointGraph.toPredimension.IsStrong
      ((Finset.univ : Finset Empty).image j)
      (Finset.univ : Finset Unit) := by
    have hEmpty : ((Finset.univ : Finset Empty).image j) =
        (∅ : Finset Unit) := by
      simp
    rw [hEmpty]
    exact GraphOn.onePointGraph.empty_strong_of_twoSparse
      GraphOn.onePointGraph_sparse
  obtain ⟨K, old, new, hOld, _, hAdjOld, _, _, hNoIdent,
      hSparseK, hStrongOld, _⟩ :=
    exists_finite_strong_free_amalgam
      G GraphOn.onePointGraph i j hi hj hAgree
      hSparse GraphOn.onePointGraph_sparse hStrongG hStrongOne
  refine ⟨K, old, new (), hOld, hAdjOld,
    hSparseK, hStrongOld, ?_⟩
  intro hMem
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hMem
  obtain ⟨p, _, _⟩ := hNoIdent v () hv
  exact Empty.elim p

end FiniteSpan
end BigHrushovski
