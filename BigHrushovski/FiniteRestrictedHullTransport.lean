import BigHrushovski.CFDClosedTransport

/-!
# Finite d-closed hulls under embeddings of restricted domains

The established induced-image lemma requires a globally injective
map preserving all edges and nonedges on the entire vertex type.
An embedding of a finite closed substructure is not such a map.

This module replaces those global hypotheses with injectivity and
inducedness **only on the finite ambient set b** in which the hull is
computed. It does so by taking the actual induced graph on the
finite subtype {v // v ∈ b}. No map or graph outside b is used in
the argument. The result is reusable for both C_0 and C_F.

An eventual set-valued functional embedding may be defined only
on its closed source domain. Its restriction to each finite
container gives exactly the interface of this lemma.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- The induced graph on an actual finite vertex set, with literal
vertex labels retained as subtype elements. -/
def finiteInducedSubtype
    (G : GraphOn U) (b : Finset U) :
    GraphOn {u : U // u ∈ b} where
  adj x y := G.adj x.val y.val
  symm := by
    intro x y h
    exact G.symm x.val y.val h
  irrefl := by
    intro x h
    exact G.irrefl x.val h

/-- Restrict a finite generator set to the literal finite subtype.
No isomorphic replacement of the selected vertices is made. -/
noncomputable def restrictFiniteSet
    (b s : Finset U) : Finset {u : U // u ∈ b} := by
  classical
  exact (Finset.univ : Finset {u : U // u ∈ b}).filter
    (fun x => x.val ∈ s)

/-- Forgetting subtype proofs returns exactly the selected finite
set, whenever it is contained in the ambient finite set. -/
theorem restrictFiniteSet_image_val
    (b s : Finset U) (hs : s ⊆ b) :
    (restrictFiniteSet b s).image
      (fun x : {u : U // u ∈ b} => x.val) = s := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    rw [← hxu]
    exact (Finset.mem_filter.mp hx).2
  · intro hu
    exact Finset.mem_image.mpr
      ⟨⟨u, hs hu⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩

/-- The entire literal finite subtype projects onto the chosen
ambient set and does not add dummy vertices. -/
theorem finiteSubtype_univ_image_val
    (b : Finset U) :
    (Finset.univ : Finset {u : U // u ∈ b}).image
      (fun x : {u : U // u ∈ b} => x.val) = b := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨x, _, hxu⟩ := Finset.mem_image.mp hu
    rw [← hxu]
    exact x.property
  · intro hu
    exact Finset.mem_image.mpr
      ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩

/-- Exact transport of finite d-closed hulls under a map which
is injective and induced **only on the finite ambient b**.
The map may behave arbitrarily outside b.

This is proved by two applications of the already validated
globally induced image theorem to the *same finite subtype*
of b: first its literal inclusion into U, then its given
embedding into V. -/
theorem dClosedHull_image_on
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V)
    (b : Finset U)
    (hf : ∀ u ∈ b, ∀ v ∈ b, f u = f v → u = v)
    (hAdj : ∀ u ∈ b, ∀ v ∈ b,
      G.adj u v ↔ H.adj (f u) (f v))
    (s : Finset U) (hs : s ⊆ b) :
    (G.toPredimension.dClosedHull s b).image f =
      H.toPredimension.dClosedHull (s.image f) (b.image f) := by
  classical
  let G₀ : GraphOn {u : U // u ∈ b} := G.finiteInducedSubtype b
  let j : {u : U // u ∈ b} → U := fun x => x.val
  let k : {u : U // u ∈ b} → V := fun x => f x.val
  let t : Finset {u : U // u ∈ b} := restrictFiniteSet b s
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext h
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    exact hf x.val x.property y.val y.property h
  have hAdjJ : ∀ x y : {u : U // u ∈ b},
      G₀.adj x y ↔ G.adj (j x) (j y) := by
    intro x y
    exact Iff.rfl
  have hAdjK : ∀ x y : {u : U // u ∈ b},
      G₀.adj x y ↔ H.adj (k x) (k y) := by
    intro x y
    exact hAdj x.val x.property y.val y.property
  have htJ : t.image j = s :=
    restrictFiniteSet_image_val b s hs
  have hbJ : (Finset.univ : Finset {u : U // u ∈ b}).image j = b :=
    finiteSubtype_univ_image_val b
  have htK : t.image k = s.image f := by
    calc
      t.image k = (t.image j).image f := by
        simp only [Finset.image_image]
        rfl
      _ = s.image f := by rw [htJ]
  have hbK :
      (Finset.univ : Finset {u : U // u ∈ b}).image k =
        b.image f := by
    calc
      (Finset.univ : Finset {u : U // u ∈ b}).image k =
          ((Finset.univ : Finset {u : U // u ∈ b}).image j).image f := by
        simp only [Finset.image_image]
        rfl
      _ = b.image f := by rw [hbJ]
  have hSource :
      (G₀.toPredimension.dClosedHull t Finset.univ).image j =
        G.toPredimension.dClosedHull s b := by
    have h := G₀.dClosedHull_image G j hj hAdjJ t Finset.univ
      (Finset.subset_univ _)
    rw [htJ, hbJ] at h
    exact h
  have hTarget :
      (G₀.toPredimension.dClosedHull t Finset.univ).image k =
        H.toPredimension.dClosedHull (s.image f) (b.image f) := by
    have h := G₀.dClosedHull_image H k hk hAdjK t Finset.univ
      (Finset.subset_univ _)
    rw [htK, hbK] at h
    exact h
  calc
    (G.toPredimension.dClosedHull s b).image f =
        ((G₀.toPredimension.dClosedHull t Finset.univ).image j).image f :=
      congrArg (Finset.image f) hSource.symm
    _ = (G₀.toPredimension.dClosedHull t Finset.univ).image k := by
      simp only [Finset.image_image]
      rfl
    _ = H.toPredimension.dClosedHull (s.image f) (b.image f) :=
      hTarget

end GraphOn
end BigHrushovski
