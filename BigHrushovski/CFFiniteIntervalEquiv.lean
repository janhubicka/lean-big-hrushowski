import BigHrushovski.CFFiniteMinimalDiagramResponse

/-!
# Canonical ordered split representation of finite C_F extension intervals

For disjoint finite vertex sets a,b of an ordered finite graph,
the induced graph on a ∪ b has a literal split presentation:
the old subtype a and the new subtype b. The new subtype
inherits its order from the ambient vertex type, and is
enumerated increasingly by Fin(card b).

We construct an explicit equivalence between the resulting
old/new split carrier and the original subtype of a ∪ b.
Its underlying vertex value is exactly the original one.
The equivalence preserves the *complete* induced graph,
including nonedges; no unspecified isomorphism or arbitrary
renaming of old vertices is involved.

This is the exact transport needed to state the finite
extension-property response directly on a prescribed
labelled target rather than an already split local graph.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFLocalCatalogue

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The complete old/new split carrier maps to the literal
vertex subset a ∪ b, with the original vertex names retained. -/
def splitIntoUnion
    (a b : Finset V) :
    Sum (OldCarrier V a) (FreshCarrier V b) →
      {v : V // v ∈ a ∪ b}
  | Sum.inl x => ⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩
  | Sum.inr y => ⟨y.val, Finset.mem_union.mpr (Or.inr y.property)⟩

/-- Injectivity requires disjointness of the original old and
fresh sets, not merely injectivity on either summand. -/
theorem splitIntoUnion_injective
    (a b : Finset V) (hDisj : Disjoint a b) :
    Function.Injective (splitIntoUnion a b) := by
  intro x y hxy
  apply splitValue_injective a b hDisj
  have hx : (splitIntoUnion a b x).val = splitValue a b x := by
    cases x <;> rfl
  have hy : (splitIntoUnion a b y).val = splitValue a b y := by
    cases y <;> rfl
  exact hx.symm.trans ((congrArg Subtype.val hxy).trans hy)

/-- Every vertex in a∪b belongs to at least one of the two
split sides; the corresponding tagged subtype gives a preimage. -/
theorem splitIntoUnion_surjective
    (a b : Finset V) :
    Function.Surjective (splitIntoUnion a b) := by
  intro x
  rcases Finset.mem_union.mp x.property with ha | hb
  · refine ⟨Sum.inl ⟨x.val, ha⟩, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨Sum.inr ⟨x.val, hb⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Canonical old/new vertex equivalence, fixing literal old
vertices and retaining the chosen new vertex names. -/
noncomputable def splitUnionEquiv
    (a b : Finset V) (hDisj : Disjoint a b) :
    Sum (OldCarrier V a) (FreshCarrier V b) ≃
      {v : V // v ∈ a ∪ b} :=
  Equiv.ofBijective (splitIntoUnion a b)
    ⟨splitIntoUnion_injective a b hDisj,
      splitIntoUnion_surjective a b⟩

/-- The complete ordered split presentation used by the tagged
local request catalogue. The fresh subtype is numbered
increasingly by Fin(card b). -/
noncomputable def orderedSplitUnionEquiv
    (a b : Finset V) (hDisj : Disjoint a b) :
    Sum (OldCarrier V a) (Fin (Fintype.card (FreshCarrier V b))) ≃
      {v : V // v ∈ a ∪ b} :=
  (Equiv.sumCongr (Equiv.refl (OldCarrier V a))
    (increasingNewBlock (B := FreshCarrier V b)).toEquiv).trans
      (splitUnionEquiv a b hDisj)

/-- Every old vertex is fixed pointwise under the ordered
presentation: no old support or old source is relabelled. -/
@[simp] theorem orderedSplitUnionEquiv_old
    (a b : Finset V) (hDisj : Disjoint a b)
    (x : OldCarrier V a) :
    (orderedSplitUnionEquiv a b hDisj (Sum.inl x)).val =
      x.val :=
  rfl

/-- The new vertices appear in exactly their inherited order. -/
@[simp] theorem orderedSplitUnionEquiv_fresh
    (a b : Finset V) (hDisj : Disjoint a b)
    (i : Fin (Fintype.card (FreshCarrier V b))) :
    (orderedSplitUnionEquiv a b hDisj (Sum.inr i)).val =
      (increasingNewBlock (B := FreshCarrier V b) i).val :=
  rfl

/-- The complete induced graph on a∪b is exactly the normalized
split graph, not just a homomorphic image. The biconditional
explicitly includes reflection of absent edges. -/
theorem orderedSplitUnion_adj_iff
    (G : GraphOn V)
    (a b : Finset V) (hDisj : Disjoint a b)
    (x y : Sum (OldCarrier V a)
      (Fin (Fintype.card (FreshCarrier V b)))) :
    ((splitGraph G a b).pullback
      (Equiv.sumCongr (Equiv.refl (OldCarrier V a))
        (increasingNewBlock (B := FreshCarrier V b)).toEquiv)).adj x y ↔
      G.adj
        (orderedSplitUnionEquiv a b hDisj x).val
        (orderedSplitUnionEquiv a b hDisj y).val := by
  cases x with
  | inl sx =>
      cases y with
      | inl sy => rfl
      | inr j => rfl
  | inr i =>
      cases y with
      | inl sy => rfl
      | inr j => rfl

end CFCoherentTower
end BigHrushovski
