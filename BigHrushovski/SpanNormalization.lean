import BigHrushovski.TaggedStrongAmalgam
import Mathlib.Logic.Equiv.Sum

/-!
# Normalizing an arbitrary injective base embedding

An injection i : P → A identifies its range with P and leaves a disjoint
complement consisting of the remaining vertices of A.  This yields an
equivalence P ⊕ Tail(i) ≃ A extending i. Pulling back a graph along the
equivalence puts a finite base embedding into the canonical tagged form
used in the verified strong free-amalgamation theorem.

The finite predimension and strongness transfer will be checked in the
next theorem layer; this module establishes the carrier equivalence and
the exact induced graph agreement on the shared base.
-/

namespace BigHrushovski

namespace FiniteSpan

variable {P A B : Type*}

/-- The vertices outside the image of an injective base map. -/
abbrev Tail (i : P → A) := {a : A // ¬ ∃ p : P, i p = a}

/-- An injective base map is an equivalence onto its image. -/
noncomputable def imageEquiv (i : P → A) (hi : Function.Injective i) :
    P ≃ {a : A // ∃ p : P, i p = a} where
  toFun p := ⟨i p, ⟨p, rfl⟩⟩
  invFun x := Classical.choose x.property
  left_inv p := by
    apply hi
    exact Classical.choose_spec
      (show ∃ q : P, i q = i p from ⟨p, rfl⟩)
  right_inv x := by
    apply Subtype.ext
    exact Classical.choose_spec x.property

/-- The whole carrier splits as its embedded base and a disjoint tail. -/
noncomputable def splitEquiv (i : P → A) (hi : Function.Injective i) :
    (P ⊕ Tail i) ≃ A := by
  classical
  exact
    (Equiv.sumCongr (imageEquiv i hi)
      (Equiv.refl (Tail i))).trans
      (Equiv.sumCompl (fun a : A => ∃ p : P, i p = a))

/-- The normal-form inclusion of the shared base is exactly i. -/
@[simp] theorem splitEquiv_inl (i : P → A) (hi : Function.Injective i)
    (p : P) :
    splitEquiv i hi (Sum.inl p) = i p := by
  rfl

/-- The other summand maps to its own vertex without identification. -/
@[simp] theorem splitEquiv_inr (i : P → A) (hi : Function.Injective i)
    (a : Tail i) :
    splitEquiv i hi (Sum.inr a) = a.val := by
  rfl

end FiniteSpan

namespace GraphOn

variable {U V : Type*}

/-- Restrict a graph relation along a map; no injectivity is required
for the pullback graph to be symmetric and irreflexive. -/
def pullback (G : GraphOn V) (f : U → V) : GraphOn U where
  adj x y := G.adj (f x) (f y)
  symm := by
    intro x y h
    exact G.symm (f x) (f y) h
  irrefl := by
    intro x h
    exact G.irrefl (f x) h

theorem pullback_adj (G : GraphOn V) (f : U → V) (x y : U) :
    (G.pullback f).adj x y ↔ G.adj (f x) (f y) :=
  Iff.rfl

end GraphOn

namespace FiniteSpan

/-- Put a graph with an arbitrary injected base into tagged normal form. -/
noncomputable def normalGraph
    (G : GraphOn A) (i : P → A) (hi : Function.Injective i) :
    GraphOn (P ⊕ Tail i) :=
  G.pullback (splitEquiv i hi)

/-- The induced adjacency on the canonical base is unchanged. -/
theorem normalGraph_base
    (G : GraphOn A) (i : P → A) (hi : Function.Injective i)
    (p q : P) :
    (normalGraph G i hi).adj (Sum.inl p) (Sum.inl q) ↔
      G.adj (i p) (i q) := by
  change G.adj (splitEquiv i hi (Sum.inl p))
    (splitEquiv i hi (Sum.inl q)) ↔ _
  simp

/-- If the original two base embeddings are compatible, their
normal-form graph structures agree on the common P-part. -/
theorem normalGraphs_agree_base
    (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P, G.adj (i p) (i q) ↔
      H.adj (j p) (j q)) :
    TaggedAmalgam.AgreeBase (normalGraph G i hi)
      (normalGraph H j hj) := by
  intro p q
  exact (normalGraph_base G i hi p q).trans
    ((hAgree p q).trans (normalGraph_base H j hj p q).symm)


section finite

variable [Fintype P] [Fintype A]
variable [DecidableEq P] [DecidableEq A]

/-- The complement of an injected base in a finite carrier is finite. -/
noncomputable instance tailFintype (i : P → A) : Fintype (Tail i) := by
  classical
  infer_instance

/-- The equivalence covers every vertex of the original finite carrier. -/
theorem splitEquiv_image_univ (i : P → A) (hi : Function.Injective i) :
    (Finset.univ : Finset (P ⊕ Tail i)).image (splitEquiv i hi) =
      (Finset.univ : Finset A) := by
  classical
  exact Finset.image_univ_of_surjective (splitEquiv i hi).surjective

/-- Under the carrier equivalence, the canonical shared base maps
exactly to the original image i(P). -/
theorem splitEquiv_base_image (i : P → A)
    (hi : Function.Injective i) :
    ((Finset.univ : Finset P).image
      (Sum.inl : P → P ⊕ Tail i)).image (splitEquiv i hi) =
      (Finset.univ : Finset P).image i := by
  classical
  rw [Finset.image_image]
  have hComp : (splitEquiv i hi) ∘
      (Sum.inl : P → P ⊕ Tail i) = i := by
    funext p
    exact splitEquiv_inl i hi p
  rw [hComp]

/-- A finite graph is 2-sparse exactly when its re-labelled normal form
is 2-sparse. The proof compares all induced finite subsets. -/
theorem normalGraph_twoSparse_iff (G : GraphOn A)
    (i : P → A) (hi : Function.Injective i) :
    (normalGraph G i hi).IsTwoSparse
      (Finset.univ : Finset (P ⊕ Tail i)) ↔
    G.IsTwoSparse (Finset.univ : Finset A) := by
  classical
  let e : (P ⊕ Tail i) ≃ A := splitEquiv i hi
  have hAdj : ∀ x y : P ⊕ Tail i,
      (normalGraph G i hi).adj x y ↔ G.adj (e x) (e y) :=
    fun _ _ => Iff.rfl
  have h := (normalGraph G i hi).twoSparse_image_iff G
    e e.injective hAdj (Finset.univ : Finset (P ⊕ Tail i))
  have hUniv : (Finset.univ : Finset (P ⊕ Tail i)).image e =
      (Finset.univ : Finset A) :=
    splitEquiv_image_univ i hi
  rw [hUniv] at h
  exact h.symm

/-- Self-sufficiency of the embedded base is invariant when a finite
graph is put into normal form P ⊕ Tail(i). -/
theorem normalGraph_strong_base_iff (G : GraphOn A)
    (i : P → A) (hi : Function.Injective i) :
    (normalGraph G i hi).toPredimension.IsStrong
      ((Finset.univ : Finset P).image (Sum.inl : P → P ⊕ Tail i))
      (Finset.univ : Finset (P ⊕ Tail i)) ↔
    G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i)
      (Finset.univ : Finset A) := by
  classical
  let e : (P ⊕ Tail i) ≃ A := splitEquiv i hi
  have hAdj : ∀ x y : P ⊕ Tail i,
      (normalGraph G i hi).adj x y ↔ G.adj (e x) (e y) :=
    fun _ _ => Iff.rfl
  have h := (normalGraph G i hi).strong_image_iff G
    e e.injective hAdj
    ((Finset.univ : Finset P).image (Sum.inl : P → P ⊕ Tail i))
    (Finset.univ : Finset (P ⊕ Tail i))
    (Finset.subset_univ _)
  have hBase :
      (((Finset.univ : Finset P).image
        (Sum.inl : P → P ⊕ Tail i)).image e) =
      (Finset.univ : Finset P).image i :=
    splitEquiv_base_image i hi
  have hUniv : (Finset.univ : Finset (P ⊕ Tail i)).image e =
      (Finset.univ : Finset A) :=
    splitEquiv_image_univ i hi
  rw [hBase, hUniv] at h
  exact h.symm

end finite


/-- Strong free amalgamation for two arbitrary finite graph structures
equipped with injective embeddings of a common base.

The output graph is explicitly the tagged free graph of the two
normalized input graphs. The conclusions are 2-sparsity of this graph
and strongness of both canonical induced factor domains. The carrier
normalizations extend the supplied base embeddings exactly.

This is a finite strong-amalgamation theorem for abstract embedded
base diagrams. Construction of the countable strong Fraisse limit
and the functional closure presentation remain separate obligations. -/
theorem strong_amalgam_of_embeddings
    [Fintype P] [Fintype A] [DecidableEq P] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i) (Finset.univ : Finset A))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j) (Finset.univ : Finset B)) :
    let F := TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)
    F.IsTwoSparse
      (Finset.univ : Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
    F.toPredimension.IsStrong
      (TaggedAmalgam.leftDomain (P := P) (L := Tail i) (R := Tail j))
      (Finset.univ : Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
    F.toPredimension.IsStrong
      (TaggedAmalgam.rightDomain (P := P) (L := Tail i) (R := Tail j))
      (Finset.univ : Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) := by
  classical
  have hAgreeN : TaggedAmalgam.AgreeBase
      (normalGraph G i hi) (normalGraph H j hj) :=
    normalGraphs_agree_base G H i j hi hj hAgree
  have hSparseGN : (normalGraph G i hi).IsTwoSparse
      (Finset.univ : Finset (P ⊕ Tail i)) :=
    (normalGraph_twoSparse_iff G i hi).mpr hSparseG
  have hSparseHN : (normalGraph H j hj).IsTwoSparse
      (Finset.univ : Finset (P ⊕ Tail j)) :=
    (normalGraph_twoSparse_iff H j hj).mpr hSparseH
  have hStrongGN : (normalGraph G i hi).toPredimension.IsStrong
      (TaggedAmalgam.leftBase (P := P) (L := Tail i))
      (Finset.univ : Finset (P ⊕ Tail i)) :=
    (normalGraph_strong_base_iff G i hi).mpr hStrongG
  have hStrongHN : (normalGraph H j hj).toPredimension.IsStrong
      (TaggedAmalgam.rightBase (P := P) (R := Tail j))
      (Finset.univ : Finset (P ⊕ Tail j)) :=
    (normalGraph_strong_base_iff H j hj).mpr hStrongH
  have h := TaggedAmalgam.tagged_strong_free_amalgam
    (normalGraph G i hi) (normalGraph H j hj)
    hAgreeN hSparseGN hSparseHN hStrongGN hStrongHN
  exact ⟨h.1, h.2.1, h.2.2.1⟩


/-- Canonical map of the original left graph into the fresh tagged carrier. -/
noncomputable def leftAmalgamEmbedding
    (i : P → A) (hi : Function.Injective i)
    {B : Type*} (j : P → B) :
    A → TaggedAmalgam.Carrier P (Tail i) (Tail j) :=
  TaggedAmalgam.leftTag ∘ (splitEquiv i hi).symm

/-- Canonical map of the original right graph into the fresh tagged carrier. -/
noncomputable def rightAmalgamEmbedding
    {B : Type*} (i : P → A)
    (j : P → B) (hj : Function.Injective j) :
    B → TaggedAmalgam.Carrier P (Tail i) (Tail j) :=
  TaggedAmalgam.rightTag ∘ (splitEquiv j hj).symm

theorem leftAmalgamEmbedding_injective
    (i : P → A) (hi : Function.Injective i)
    {B : Type*} (j : P → B) :
    Function.Injective (leftAmalgamEmbedding i hi j) := by
  intro x y h
  apply (splitEquiv i hi).symm.injective
  exact TaggedAmalgam.leftTag_injective h

theorem rightAmalgamEmbedding_injective
    {B : Type*} (i : P → A)
    (j : P → B) (hj : Function.Injective j) :
    Function.Injective (rightAmalgamEmbedding i j hj) := by
  intro x y h
  apply (splitEquiv j hj).symm.injective
  exact TaggedAmalgam.rightTag_injective h

/-- The two embeddings identify exactly the prescribed image of the
abstract common base. -/
theorem amalgamEmbeddings_agree_base
    {B : Type*} (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (p : P) :
    leftAmalgamEmbedding i hi j (i p) =
      rightAmalgamEmbedding i j hj (j p) := by
  have hl : (splitEquiv i hi).symm (i p) = Sum.inl p := by
    apply (splitEquiv i hi).injective
    simp
  have hr : (splitEquiv j hj).symm (j p) = Sum.inl p := by
    apply (splitEquiv j hj).injective
    simp
  change TaggedAmalgam.leftTag ((splitEquiv i hi).symm (i p)) =
    TaggedAmalgam.rightTag ((splitEquiv j hj).symm (j p))
  rw [hl, hr]
  rfl

/-- The left map preserves and reflects the entire induced adjacency
relation, not merely edges. -/
theorem leftAmalgamEmbedding_induced
    {B : Type*} (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (a b : A) :
    (TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)).adj
      (leftAmalgamEmbedding i hi j a)
      (leftAmalgamEmbedding i hi j b) ↔ G.adj a b := by
  have hAgreeN :=
    normalGraphs_agree_base G H i j hi hj hAgree
  change (TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)).adj
      (TaggedAmalgam.leftTag ((splitEquiv i hi).symm a))
      (TaggedAmalgam.leftTag ((splitEquiv i hi).symm b)) ↔ G.adj a b
  rw [TaggedAmalgam.freeGraph_left
    (normalGraph G i hi) (normalGraph H j hj) hAgreeN]
  change G.adj (splitEquiv i hi ((splitEquiv i hi).symm a))
    (splitEquiv i hi ((splitEquiv i hi).symm b)) ↔ G.adj a b
  simp

/-- The right map is likewise an induced graph embedding. -/
theorem rightAmalgamEmbedding_induced
    {B : Type*} (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (a b : B) :
    (TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)).adj
      (rightAmalgamEmbedding i j hj a)
      (rightAmalgamEmbedding i j hj b) ↔ H.adj a b := by
  have hAgreeN :=
    normalGraphs_agree_base G H i j hi hj hAgree
  change (TaggedAmalgam.freeGraph
      (normalGraph G i hi) (normalGraph H j hj)).adj
      (TaggedAmalgam.rightTag ((splitEquiv j hj).symm a))
      (TaggedAmalgam.rightTag ((splitEquiv j hj).symm b)) ↔ H.adj a b
  rw [TaggedAmalgam.freeGraph_right
    (normalGraph G i hi) (normalGraph H j hj) hAgreeN]
  change H.adj (splitEquiv j hj ((splitEquiv j hj).symm a))
    (splitEquiv j hj ((splitEquiv j hj).symm b)) ↔ H.adj a b
  simp


/-- The image of the original left carrier is exactly the tagged left
domain, since the normalization equivalence is surjective. -/
theorem leftAmalgamEmbedding_image_univ
    [Fintype P] [Fintype A] [DecidableEq P] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    (i : P → A) (hi : Function.Injective i) (j : P → B) :
    (Finset.univ : Finset A).image (leftAmalgamEmbedding i hi j) =
      TaggedAmalgam.leftDomain (P := P) (L := Tail i) (R := Tail j) := by
  classical
  change (Finset.univ : Finset A).image
    ((TaggedAmalgam.leftTag :
      P ⊕ Tail i → TaggedAmalgam.Carrier P (Tail i) (Tail j)) ∘
      (splitEquiv i hi).symm) =
    (Finset.univ : Finset (P ⊕ Tail i)).image
      (TaggedAmalgam.leftTag :
        P ⊕ Tail i → TaggedAmalgam.Carrier P (Tail i) (Tail j))
  rw [← Finset.image_image]
  rw [Finset.image_univ_of_surjective (splitEquiv i hi).symm.surjective]

/-- The image of the original right carrier is precisely the tagged
right domain. -/
theorem rightAmalgamEmbedding_image_univ
    [Fintype P] [Fintype A] [DecidableEq P] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    (i : P → A) (j : P → B) (hj : Function.Injective j) :
    (Finset.univ : Finset B).image (rightAmalgamEmbedding i j hj) =
      TaggedAmalgam.rightDomain (P := P) (L := Tail i) (R := Tail j) := by
  classical
  change (Finset.univ : Finset B).image
    ((TaggedAmalgam.rightTag :
      P ⊕ Tail j → TaggedAmalgam.Carrier P (Tail i) (Tail j)) ∘
      (splitEquiv j hj).symm) =
    (Finset.univ : Finset (P ⊕ Tail j)).image
      (TaggedAmalgam.rightTag :
        P ⊕ Tail j → TaggedAmalgam.Carrier P (Tail i) (Tail j))
  rw [← Finset.image_image]
  rw [Finset.image_univ_of_surjective (splitEquiv j hj).symm.surjective]

/-- The original input structures have no accidental identifications:
equality between their two tagged images comes only from one base point. -/
theorem amalgamEmbeddings_identify_only_base
    {B : Type*} (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    {a : A} {b : B}
    (hab : leftAmalgamEmbedding i hi j a =
      rightAmalgamEmbedding i j hj b) :
    ∃ p : P, a = i p ∧ b = j p := by
  have hTag : TaggedAmalgam.leftTag ((splitEquiv i hi).symm a) =
      TaggedAmalgam.rightTag ((splitEquiv j hj).symm b) := hab
  obtain ⟨p, hpA, hpB⟩ := TaggedAmalgam.leftTag_eq_rightTag hTag
  refine ⟨p, ?_, ?_⟩
  · have hh := congrArg (splitEquiv i hi) hpA
    simpa using hh
  · have hh := congrArg (splitEquiv j hj) hpB
    simpa using hh

/-- An explicit strong free-amalgamation witness for any finite pair of
2-sparse graphs over a common strong abstract base.

K is a graph on the finite tagged carrier, and f,g are embeddings of
the *original* graph types. They agree exactly on the prescribed base,
preserve and reflect adjacency, and their images are strong in K.
The free-amalgamation property is thus established for arbitrary finite
induced strong embedding spans, not only for pre-normalized presentations.
-/
theorem exists_finite_strong_free_amalgam
    [Fintype P] [Fintype A] [DecidableEq P] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    (G : GraphOn A) (H : GraphOn B)
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i) (Finset.univ : Finset A))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j) (Finset.univ : Finset B)) :
    ∃ (K : GraphOn (TaggedAmalgam.Carrier P (Tail i) (Tail j)))
      (f : A → TaggedAmalgam.Carrier P (Tail i) (Tail j))
      (g : B → TaggedAmalgam.Carrier P (Tail i) (Tail j)),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ x y : A, K.adj (f x) (f y) ↔ G.adj x y) ∧
      (∀ x y : B, K.adj (g x) (g y) ↔ H.adj x y) ∧
      (∀ p : P, f (i p) = g (j p)) ∧
      (∀ x : A, ∀ y : B, f x = g y →
        ∃ p : P, x = i p ∧ y = j p) ∧
      K.IsTwoSparse (Finset.univ :
        Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset A).image f) Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset B).image g) Finset.univ := by
  classical
  let K := TaggedAmalgam.freeGraph
    (normalGraph G i hi) (normalGraph H j hj)
  let f := leftAmalgamEmbedding i hi j
  let g := rightAmalgamEmbedding i j hj
  have h := strong_amalgam_of_embeddings
    G H i j hi hj hAgree hSparseG hSparseH hStrongG hStrongH
  refine ⟨K, f, g,
    leftAmalgamEmbedding_injective i hi j,
    rightAmalgamEmbedding_injective i j hj,
    ?_, ?_, ?_, ?_, h.1, ?_, ?_⟩
  · intro x y
    exact leftAmalgamEmbedding_induced G H i j hi hj hAgree x y
  · intro x y
    exact rightAmalgamEmbedding_induced G H i j hi hj hAgree x y
  · intro p
    exact amalgamEmbeddings_agree_base i j hi hj p
  · intro x y hxy
    exact amalgamEmbeddings_identify_only_base i j hi hj hxy
  · have hImage := leftAmalgamEmbedding_image_univ i hi j
    rw [hImage]
    exact h.2.1
  · have hImage := rightAmalgamEmbedding_image_univ i j hj
    rw [hImage]
    exact h.2.2

end FiniteSpan
end BigHrushovski
