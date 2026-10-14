import BigHrushovski.C0MinimalImage
import BigHrushovski.UnlabelledExtension
import BigHrushovski.GenericFraisseConstruction
import BigHrushovski.C0PrefixClosure

/-!
# Realising one minimal strong block over a fixed strong prefix in M0

The generic graph has the labelled finite strong extension property.
This module transfers it to a *literal* finite minimal strong step
whose old carrier is a subtype of a chosen finite globally strong
prefix a ⊆ ℕ.

Unlike a graph-level free-amalgamation identity, the conclusion gives
an actual induced embedding into the constructed M0, fixing every
vertex of a pointwise, with globally strong finite image and a
minimal strong extension from a to that image.

The finite input graph K can be freely attached from a prescribed
local component by the already verified C0 local-free-minimality lemma.
The theorem does not impose the chosen unary closure on M0: its
position in a newly constructed countable functional enumeration and
the fair functional request schedule are separate obligations.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- All vertices in the subtype of a finite set a are precisely a. -/
private theorem subtype_univ_image_eq (a : Finset ℕ) :
    (Finset.univ : Finset {v : ℕ // v ∈ a}).image
      (Subtype.val : {v : ℕ // v ∈ a} → ℕ) = a := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
    rw [← hx]
    exact x.property
  · intro hv
    exact Finset.mem_image.mpr
      ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

/-- Any prescribed finite minimal strong extension of the *induced*
old prefix has an actual copy in a strong generic graph, with the old
vertex labels fixed exactly. Its entire finite image is globally strong
and it is still a minimal strong extension of the prescribed prefix.

The conclusion does not say the image is one block of a pre-existing
enumeration: this theorem is the finite response used to *construct*
a new enumeration satisfying functional requests. -/
theorem realizes_minimalStrongStep_over_prefix
    (M : GraphOn ℕ) (hExt : HasStrongExtensionProperty M)
    (a : Finset ℕ)
    (ha : M.toPredimension.IsGloballyStrong a)
    {B : Type*} [Fintype B] [DecidableEq B]
    (K : GraphOn (Sum {v : ℕ // v ∈ a} B))
    (hSparseK : K.IsTwoSparse
      (Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)))
    (hOld : ∀ x y : {v : ℕ // v ∈ a},
      K.adj (.inl x) (.inl y) ↔ M.adj x.val y.val)
    (hMin : K.toPredimension.IsMinimalStrongStep
      ((Finset.univ : Finset {v : ℕ // v ∈ a}).image Sum.inl)
      (Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B))) :
    ∃ g : Sum {v : ℕ // v ∈ a} B → ℕ,
      Function.Injective g ∧
      (∀ x y : Sum {v : ℕ // v ∈ a} B,
        K.adj x y ↔ M.adj (g x) (g y)) ∧
      (∀ x : {v : ℕ // v ∈ a}, g (.inl x) = x.val) ∧
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)).image g) ∧
      M.toPredimension.IsMinimalStrongStep a
        ((Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)).image g) := by
  classical
  let A := {v : ℕ // v ∈ a}
  let i : A → Sum A B := Sum.inl
  let GA : GraphOn A := K.pullback i
  have hi : Function.Injective i := Sum.inl_injective
  have hAdjI : ∀ x y : A, GA.adj x y ↔ K.adj (i x) (i y) :=
    fun _ _ => Iff.rfl
  have hSparseSource : GA.IsTwoSparse (Finset.univ : Finset A) := by
    apply (GA.twoSparse_image_iff K i hi hAdjI
      (Finset.univ : Finset A)).mp
    exact K.twoSparse_substructure hSparseK (Finset.subset_univ _)
  have hImageOld : (Finset.univ : Finset A).image
      (Subtype.val : A → ℕ) = a :=
    subtype_univ_image_eq a
  have hSourceGlobal :
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset A).image (Subtype.val : A → ℕ)) := by
    rw [hImageOld]
    exact ha
  have hAdjOld : ∀ x y : A, GA.adj x y ↔ M.adj x.val y.val :=
    fun x y => hOld x y
  obtain ⟨g, hgInj, hgAdj, hgBase, hgGlobal⟩ :=
    arbitrary_finite_strong_extension M hExt
      GA K i hi hAdjI hSparseSource hSparseK hMin.1
      (Subtype.val : A → ℕ) Subtype.val_injective
      hAdjOld hSourceGlobal
  have hImageBase :
      ((Finset.univ : Finset A).image i).image g = a := by
    rw [Finset.image_image]
    have hfun : g ∘ i = (Subtype.val : A → ℕ) := by
      funext x
      exact hgBase x
    rw [hfun, hImageOld]
  have hMinimalImage :
      M.toPredimension.IsMinimalStrongStep
        (((Finset.univ : Finset A).image i).image g)
        ((Finset.univ : Finset (Sum A B)).image g) :=
    (K.minimalStrongStep_image_iff M g hgInj hgAdj
      ((Finset.univ : Finset A).image i)
      (Finset.univ : Finset (Sum A B))
      (Finset.subset_univ _)).mpr hMin
  rw [hImageBase] at hMinimalImage
  exact ⟨g, hgInj, hgAdj, hgBase, hgGlobal, hMinimalImage⟩

/-- The same statement for the concrete countable Hrushovski generic,
with no abstract extension-property assumption. -/
theorem genericC0_realizes_minimalStrongStep_over_prefix
    (a : Finset ℕ)
    (ha : genericTwoSparseGraph.toPredimension.IsGloballyStrong a)
    {B : Type*} [Fintype B] [DecidableEq B]
    (K : GraphOn (Sum {v : ℕ // v ∈ a} B))
    (hSparseK : K.IsTwoSparse
      (Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)))
    (hOld : ∀ x y : {v : ℕ // v ∈ a},
      K.adj (.inl x) (.inl y) ↔ genericTwoSparseGraph.adj x.val y.val)
    (hMin : K.toPredimension.IsMinimalStrongStep
      ((Finset.univ : Finset {v : ℕ // v ∈ a}).image Sum.inl)
      (Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B))) :
    ∃ g : Sum {v : ℕ // v ∈ a} B → ℕ,
      Function.Injective g ∧
      (∀ x y : Sum {v : ℕ // v ∈ a} B,
        K.adj x y ↔ genericTwoSparseGraph.adj (g x) (g y)) ∧
      (∀ x : {v : ℕ // v ∈ a}, g (.inl x) = x.val) ∧
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)).image g) ∧
      genericTwoSparseGraph.toPredimension.IsMinimalStrongStep a
        ((Finset.univ : Finset (Sum {v : ℕ // v ∈ a} B)).image g) :=
  realizes_minimalStrongStep_over_prefix genericTwoSparseGraph
    genericTwoSparseGraph_strongExtension a ha K hSparseK hOld hMin

end FiniteCatalogue
end BigHrushovski
