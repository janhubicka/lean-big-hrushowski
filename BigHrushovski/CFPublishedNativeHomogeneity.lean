import BigHrushovski.CFPublishedStrongHomogeneity

/-!
# Strong homogeneity on the original C_F birth carrier

The previous strict d-closed homogeneity theorem accepts a finite
partial isomorphism between subgraphs of a Nat relabelling. This file
removes that bookkeeping from the mathematical theorem: an arbitrary
finite induced partial isomorphism of *actual birth vertices*, whose
source and target are globally strictly d-closed, extends pointwise to
a graph automorphism on the original birth-labelled vertex set.

The key reusable step is the canonical equivalence between a finite
subtype of any carrier V and its inverse image under a genuine
equivalence Nat ≃ V. This moves both the finite graph and its old map
without creating new vertex names or altering the complete adjacency
relation. Global strict d-closure is transported by the already proved
pullback equivalence, not by a weak-strong approximation.

No comparison Fraisse limit, dummy vertices, pre-existing
automorphism or functional R/H preservation is assumed.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

variable {V : Type*} [DecidableEq V]

/-- The exact finite subtype over a subset a of V can be
identified with its inverse-image subtype under a genuine
carrier equivalence, preserving the *literal* values. -/
private noncomputable def finitePullbackSubtypeEquiv
    (ι : ℕ ≃ V) (a : Finset V) :
    {n : ℕ // n ∈ a.image ι.symm} ≃ {v : V // v ∈ a} := by
  classical
  refine {
    toFun := fun x => ⟨ι x.val, ?_⟩
    invFun := fun x =>
      ⟨ι.symm x.val,
        Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp x.property
    have hEq : v = ι x.val := by
      calc
        v = ι (ι.symm v) := (ι.apply_symm_apply v).symm
        _ = ι x.val := congrArg ι hval
    rwa [← hEq]
  · intro x
    apply Subtype.ext
    exact ι.symm_apply_apply x.val
  · intro x
    apply Subtype.ext
    exact ι.apply_symm_apply x.val

@[simp] private theorem finitePullbackSubtypeEquiv_apply_val
    (ι : ℕ ≃ V) (a : Finset V)
    (x : {n : ℕ // n ∈ a.image ι.symm}) :
    (finitePullbackSubtypeEquiv ι a x).val = ι x.val := rfl

@[simp] private theorem finitePullbackSubtypeEquiv_symm_apply_val
    (ι : ℕ ≃ V) (a : Finset V)
    (x : {v : V // v ∈ a}) :
    ((finitePullbackSubtypeEquiv ι a).symm x).val =
      ι.symm x.val := rfl

/-- The finite original-carrier partial isomorphism transfers
canonically to the Nat numbering. Both endpoint images are
strictly d-closed in the *whole* numbered graph, rather than
merely in a containing finite stage. -/
private noncomputable def finiteDClosedPartialIso_pullback
    (G : GraphOn V) (ι : ℕ ≃ V)
    (a b : Finset V)
    (p : {v : V // v ∈ a} ≃ {v : V // v ∈ b})
    (ha : G.toPredimension.IsGloballyDClosed a)
    (hb : G.toPredimension.IsGloballyDClosed b)
    (hp : ∀ x y : {v : V // v ∈ a},
      G.adj x.val y.val ↔ G.adj (p x).val (p y).val) :
    PartialIso (G.pullback ι) (G.pullback ι) := by
  classical
  let A := finitePullbackSubtypeEquiv ι a
  let B := finitePullbackSubtypeEquiv ι b
  refine {
    source := a.image ι.symm
    target := b.image ι.symm
    equiv := A.trans (p.trans B.symm)
    source_global := ?_
    target_global := ?_
    induced := ?_
  }
  · apply (G.globallyDClosed_pullback_iff ι (a.image ι.symm)).2
    simpa [Finset.image_image, Function.comp_def] using ha
  · apply (G.globallyDClosed_pullback_iff ι (b.image ι.symm)).2
    simpa [Finset.image_image, Function.comp_def] using hb
  · intro x y
    change G.adj (ι x.val) (ι y.val) ↔
      G.adj (ι ((A.trans (p.trans B.symm) x).val))
        (ι ((A.trans (p.trans B.symm) y).val))
    have hAx : (A x).val = ι x.val := rfl
    have hAy : (A y).val = ι y.val := rfl
    have hBx : (p (A x)).val =
        ι ((A.trans (p.trans B.symm) x).val) := by
      change (p (A x)).val = ι ((B.symm (p (A x))).val)
      exact (congrArg Subtype.val
        (B.apply_symm_apply (p (A x)))).symm
    have hBy : (p (A y)).val =
        ι ((A.trans (p.trans B.symm) y).val) := by
      change (p (A y)).val = ι ((B.symm (p (A y))).val)
      exact (congrArg Subtype.val
        (B.apply_symm_apply (p (A y)))).symm
    calc
      G.adj (ι x.val) (ι y.val) ↔
          G.adj (A x).val (A y).val := by rw [hAx, hAy]
      _ ↔ G.adj (p (A x)).val (p (A y)).val := hp (A x) (A y)
      _ ↔ G.adj (ι ((A.trans (p.trans B.symm) x).val))
            (ι ((A.trans (p.trans B.symm) y).val)) := by rw [hBx, hBy]

/-- Transport a graph automorphism extending the numbered partial
map back to an automorphism extending the original, *unnumbered*
partial map pointwise. The conclusion refers only to original V
vertices; the choice of numbering does not occur in the statement. -/
theorem nativeHomogeneity_of_numbered
    (G : GraphOn V) (ι : ℕ ≃ V)
    (a b : Finset V)
    (p : {v : V // v ∈ a} ≃ {v : V // v ∈ b})
    (ha : G.toPredimension.IsGloballyDClosed a)
    (hb : G.toPredimension.IsGloballyDClosed b)
    (hp : ∀ x y : {v : V // v ∈ a},
      G.adj x.val y.val ↔ G.adj (p x).val (p y).val)
    (hExtend : ∀ q : PartialIso (G.pullback ι) (G.pullback ι),
      ∃ β : V ≃ V,
        (∀ x y : V, G.adj x y ↔ G.adj (β x) (β y)) ∧
        (∀ x : {n : ℕ // n ∈ q.source},
          β (ι x.val) = ι (q.equiv x).val)) :
    ∃ β : V ≃ V,
      (∀ x y : V, G.adj x y ↔ G.adj (β x) (β y)) ∧
      (∀ x : {v : V // v ∈ a},
        β x.val = (p x).val) := by
  classical
  let A := finitePullbackSubtypeEquiv ι a
  let B := finitePullbackSubtypeEquiv ι b
  let q : PartialIso (G.pullback ι) (G.pullback ι) :=
    finiteDClosedPartialIso_pullback G ι a b p ha hb hp
  obtain ⟨β, hβAdj, hβOld⟩ := hExtend q
  refine ⟨β, hβAdj, ?_⟩
  intro x
  let nx : {n : ℕ // n ∈ a.image ι.symm} := A.symm x
  have hx : ι nx.val = x.val := by
    have h := congrArg Subtype.val (A.apply_symm_apply x)
    exact h
  have hq : ι (q.equiv nx).val = (p x).val := by
    change ι ((A.trans (p.trans B.symm) nx).val) = (p x).val
    simp only [Equiv.trans_apply]
    rw [A.apply_symm_apply x]
    exact congrArg Subtype.val (B.apply_symm_apply (p x))
  calc
    β x.val = β (ι nx.val) := by rw [hx]
    _ = ι (q.equiv nx).val := hβOld nx
    _ = (p x).val := hq

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- Under exactly the published C_F class assumptions, every
induced isomorphism between finite *globally strictly d-closed*
subgraphs of the actual canonical birth graph extends pointwise
to an automorphism of that graph.

The finite source and target are on the original birth-labelled
carrier, not on Nat. The proof chooses an enumeration internally
using the certified genuine strong Fraisse-limit presentation,
then transports the finite partial isomorphism through that
enumeration and applies the strict back-and-forth automorphism.
No automorphism or external Fraisse-limit isomorphism is assumed. -/
theorem publishedBirth_strongHomogeneous
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass
      (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2)
    (a b : Finset (PublishedBirthVertex F hMono hUnbounded))
    (p : {v : PublishedBirthVertex F hMono hUnbounded // v ∈ a} ≃
      {v : PublishedBirthVertex F hMono hUnbounded // v ∈ b})
    (ha : (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed a)
    (hb : (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed b)
    (hp : ∀ x y : {v : PublishedBirthVertex F hMono hUnbounded // v ∈ a},
      (publishedCountableGraph F hMono hUnbounded).adj x.val y.val ↔
        (publishedCountableGraph F hMono hUnbounded).adj
          (p x).val (p y).val) :
    ∃ β : PublishedBirthVertex F hMono hUnbounded ≃
        PublishedBirthVertex F hMono hUnbounded,
      (∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          (publishedCountableGraph F hMono hUnbounded).adj
            (β x) (β y)) ∧
      (∀ x : {v : PublishedBirthVertex F hMono hUnbounded // v ∈ a},
        β x.val = (p x).val) := by
  classical
  let G := publishedCountableGraph F hMono hUnbounded
  let ι := (publishedBirth_standardStrongFraisseLimitPresentation
    F hZero hMono hUnbounded hFree hEmptyClass hSingleton).enumerate
  apply nativeHomogeneity_of_numbered G ι a b p ha hb hp
  intro q
  exact publishedBirth_strongHomogeneous_onCarrier
    F hZero hMono hUnbounded hFree ι q

end CFCoherentTower
end BigHrushovski
