import BigHrushovski.SpanNormalization

/-!
# Elementary properties of the finite strong age C0

The graph predimension is δ(X)=2|X|-|E(X)|. In a 2-sparse graph the
empty substructure is strong, so finite strong amalgamation yields
joint embedding. The hereditary property is immediate from the
subset-wise definition of 2-sparsity.

These are the finite age properties, not the construction of its
countable strong Fraïssé limit.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The empty graph has predimension zero in any ambient graph. -/
theorem predim_empty : G.predim (∅ : Finset V) = 0 := by
  classical
  simp [predim, edgesWithin, IsEdge]

/-- Every induced subgraph of a 2-sparse graph is 2-sparse. -/
theorem twoSparse_substructure {a b : Finset V}
    (hb : G.IsTwoSparse b) (hab : a ⊆ b) :
    G.IsTwoSparse a := by
  intro s hs
  exact hb s (hs.trans hab)

/-- The empty induced subgraph is strong in every 2-sparse graph. -/
theorem empty_strong_of_twoSparse {b : Finset V}
    (hb : G.IsTwoSparse b) :
    G.toPredimension.IsStrong ∅ b := by
  refine ⟨Finset.empty_subset _, ?_⟩
  intro s _ hs
  change G.predim ∅ ≤ G.predim s
  rw [G.predim_empty]
  exact hb s hs

/-- Every induced graph on the empty vertex set is 2-sparse. -/
theorem twoSparse_empty : G.IsTwoSparse ∅ := by
  intro s hs
  have h : s = ∅ := Finset.subset_empty.mp hs
  subst s
  rw [G.predim_empty]

end GraphOn

namespace FiniteSpan

/-- The canonical disjoint-union carrier obtained by amalgamating over
the empty base. -/
abbrev JointCarrier (A B : Type*) :=
  TaggedAmalgam.Carrier Empty
    (Tail (fun e : Empty => (Empty.elim e : A)))
    (Tail (fun e : Empty => (Empty.elim e : B)))

/-- The finite strong class C0 has joint embedding, with two induced
strong embeddings into a finite 2-sparse graph. The result follows
from free amalgamation over the empty strong base. -/
theorem exists_strong_joint_embedding
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : GraphOn A) (H : GraphOn B)
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ (K : GraphOn (JointCarrier A B))
      (f : A → JointCarrier A B) (g : B → JointCarrier A B),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ x y : A, K.adj (f x) (f y) ↔ G.adj x y) ∧
      (∀ x y : B, K.adj (g x) (g y) ↔ H.adj x y) ∧
      K.IsTwoSparse (Finset.univ : Finset (JointCarrier A B)) ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset A).image f) Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset B).image g) Finset.univ := by
  classical
  let i : Empty → A := Empty.elim
  let j : Empty → B := Empty.elim
  have hi : Function.Injective i := fun p _ _ => Empty.elim p
  have hj : Function.Injective j := fun p _ _ => Empty.elim p
  have hagree : ∀ p q : Empty,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q) := by
    intro p
    exact Empty.elim p
  have hgi : G.toPredimension.IsStrong
      ((Finset.univ : Finset Empty).image i)
      (Finset.univ : Finset A) := by
    have heq : ((Finset.univ : Finset Empty).image i) = ∅ := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, _, _⟩ := Finset.mem_image.mp hx
        exact Empty.elim p
      · intro hx
        simp at hx
    rw [heq]
    exact G.empty_strong_of_twoSparse hSparseG
  have hgj : H.toPredimension.IsStrong
      ((Finset.univ : Finset Empty).image j)
      (Finset.univ : Finset B) := by
    have heq : ((Finset.univ : Finset Empty).image j) = ∅ := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, _, _⟩ := Finset.mem_image.mp hx
        exact Empty.elim p
      · intro hx
        simp at hx
    rw [heq]
    exact H.empty_strong_of_twoSparse hSparseH
  obtain ⟨K, f, g, hf, hg, hAdjF, hAdjG, _, _, hSparseK,
      hStrongF, hStrongG⟩ :=
    exists_finite_strong_free_amalgam G H i j hi hj
      hagree hSparseG hSparseH hgi hgj
  exact ⟨K, f, g, hf, hg, hAdjF, hAdjG,
    hSparseK, hStrongF, hStrongG⟩

end FiniteSpan
end BigHrushovski
