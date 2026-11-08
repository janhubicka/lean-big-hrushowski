import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Recover a complete old support from the image of a whole block

The auxiliary C_F value of a vertex in a fresh block is the
disjoint union P ∪ B of its complete named old support and
its complete fresh block. If an injective map carries P ∪ B
onto Q ∪ C and carries B onto C, then it necessarily
carries P onto Q.

This purely finite-set lemma has no predimension, order,
birth-level or graph assumptions. It can be reused for
complete component/block values in the C_0 and C_F
functional presentations without duplicating the argument.
-/

namespace BigHrushovski

/-- Full value transport and whole-block transport force
the old support image, provided each old support is
disjoint from its fresh block and f is injective.
In particular, equality of complete values is essential:
one-sided image inclusion does not imply the conclusion. -/
theorem completeBlock_supportImage
    {U V : Type*} [DecidableEq U] [DecidableEq V]
    (P B : Finset U) (Q C : Finset V)
    (f : U → V) (hf : Function.Injective f)
    (hSourceDisjoint : ∀ u ∈ P, u ∉ B)
    (hTargetDisjoint : ∀ v ∈ Q, v ∉ C)
    (hFull : (P ∪ B).image f = Q ∪ C)
    (hBlock : B.image f = C) :
    P.image f = Q := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hy
    have hWhole : y ∈ Q ∪ C := by
      rw [← hFull]
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_union.mpr (Or.inl hu), huy⟩
    rcases Finset.mem_union.mp hWhole with hq | hc
    · exact hq
    · have hbImage : y ∈ B.image f := by
        rw [hBlock]
        exact hc
      obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hbImage
      have hub : u = b := hf (huy.trans hby.symm)
      have huB : u ∈ B := by
        simpa [hub] using hb
      exact False.elim (hSourceDisjoint u hu huB)
  · intro hq
    have hWhole : y ∈ (P ∪ B).image f := by
      rw [hFull]
      exact Finset.mem_union.mpr (Or.inl hq)
    obtain ⟨u, huUnion, huy⟩ := Finset.mem_image.mp hWhole
    rcases Finset.mem_union.mp huUnion with huP | huB
    · exact Finset.mem_image.mpr ⟨u, huP, huy⟩
    · have hc : y ∈ C := by
        rw [← hBlock]
        exact Finset.mem_image.mpr ⟨u, huB, huy⟩
      exact False.elim (hTargetDisjoint y hq hc)

end BigHrushovski
