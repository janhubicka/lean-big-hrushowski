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

end FiniteSpan
end BigHrushovski
