import BigHrushovski.FiniteBlockSupportRigidity
import Mathlib.Data.Finset.Basic

/-!
# Complete-support rigidity for genuinely partial finite embeddings

A finite functional embedding is defined only on a selected closed
finite source S, not on the entire countable graph. The generic
support-recovery lemma remains valid in this situation: take the
literal preimages of the named support and the complete fresh block
inside the subtype S, and apply the finite-set equality argument
there, without inventing an extension U → V.

The result is independent of graph class, predimension, and order.
It is usable for component values in C_0 and block values in C_F.
-/

namespace BigHrushovski

/-- The literal vertices of a finite set P selected inside a
genuinely partial finite source S. -/
noncomputable def selectedFiniteSet
    {U : Type*} [DecidableEq U]
    (S P : Finset U) : Finset {u : U // u ∈ S} := by
  classical
  exact Finset.univ.filter (fun u => u.val ∈ P)

/-- Selection commutes with union without any supposition that
P or B is already contained in the selected source S. -/
theorem selectedFiniteSet_union
    {U : Type*} [DecidableEq U]
    (S P B : Finset U) :
    selectedFiniteSet S (P ∪ B) =
      selectedFiniteSet S P ∪ selectedFiniteSet S B := by
  classical
  ext u
  simp [selectedFiniteSet, Finset.mem_union]

/-- If P is contained in S, the selected subtype contains exactly
the original literal P, not just an isomorphic finite copy. -/
theorem selectedFiniteSet_image_val
    {U : Type*} [DecidableEq U]
    (S P : Finset U) (hPS : P ⊆ S) :
    (selectedFiniteSet S P).image
      (fun u : {x : U // x ∈ S} => u.val) = P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    have hp : u.val ∈ P := by
      simpa [selectedFiniteSet] using hu
    simpa [← hux] using hp
  · intro hp
    exact Finset.mem_image.mpr
      ⟨⟨x, hPS hp⟩, by simp [selectedFiniteSet, hp], rfl⟩

/-- For an injection defined ONLY on the selected finite subtype
S, preservation of its complete support-plus-block value and
the entire block image forces transport of its exact old support.
No total extension U→V is introduced or required. -/
theorem completeBlock_supportImage_partial
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (S P B : Finset U) (Q C : Finset V)
    (e : {u : U // u ∈ S} → V)
    (he : Function.Injective e)
    (hSourceDisjoint : ∀ u ∈ P, u ∉ B)
    (hTargetDisjoint : ∀ v ∈ Q, v ∉ C)
    (hFull :
      (selectedFiniteSet S (P ∪ B)).image e = Q ∪ C)
    (hBlock :
      (selectedFiniteSet S B).image e = C) :
    (selectedFiniteSet S P).image e = Q := by
  classical
  have hSource :
      ∀ u ∈ selectedFiniteSet S P,
        u ∉ selectedFiniteSet S B := by
    intro u huP huB
    have hp : u.val ∈ P := by
      simpa [selectedFiniteSet] using huP
    have hb : u.val ∈ B := by
      simpa [selectedFiniteSet] using huB
    exact hSourceDisjoint u.val hp hb
  have hFull' :
      ((selectedFiniteSet S P) ∪
        (selectedFiniteSet S B)).image e = Q ∪ C := by
    rw [← selectedFiniteSet_union]
    exact hFull
  exact completeBlock_supportImage
    (selectedFiniteSet S P) (selectedFiniteSet S B)
    Q C e he hSource hTargetDisjoint hFull' hBlock

end BigHrushovski
