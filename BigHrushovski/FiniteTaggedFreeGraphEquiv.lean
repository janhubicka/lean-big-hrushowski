import BigHrushovski.TaggedAmalgam
import Mathlib.Logic.Equiv.Sum

/-!
# Transport of a tagged free graph under tail equivalences

The free graph on a common base P and disjoint tails L,R has a
concrete carrier P ⊕ (L ⊕ R). Replacing the two tails by
equivalent carriers should not change the graph, provided the
two factor graphs are transported with their complete adjacency
relations. This is proved by mapping the defining edge witnesses
in both directions.

The result is generic: no predimension, sparsity, closure or local
order hypothesis is needed. It will be used to compare the
normalized finite C₀ functional amalgam with a tagged graph built
from the literal exclusive parts of two finite closed subsets.
The same argument is available for C_F.
-/

namespace BigHrushovski
namespace FiniteSetUnion

variable {P L R L' R' : Type*}

/-- Replace the tail of a shared-base factor while keeping each
base vertex fixed. -/
def factorTailEquiv (l : L ≃ L') :
    (P ⊕ L) ≃ (P ⊕ L') :=
  Equiv.sumCongr (Equiv.refl P) l

/-- Simultaneously replace both disjoint tails of a tagged carrier,
without changing or duplicating any common-base point. -/
def taggedTailsEquiv (l : L ≃ L') (r : R ≃ R') :
    TaggedAmalgam.Carrier P L R ≃
      TaggedAmalgam.Carrier P L' R' :=
  Equiv.sumCongr (Equiv.refl P) (Equiv.sumCongr l r)

/-- The left tag commutes exactly with the equivalence of its tail. -/
theorem taggedTailsEquiv_leftTag
    (l : L ≃ L') (r : R ≃ R')
    (u : P ⊕ L) :
    taggedTailsEquiv l r (TaggedAmalgam.leftTag u) =
      TaggedAmalgam.leftTag (factorTailEquiv l u) := by
  cases u with
  | inl p => rfl
  | inr v => rfl

/-- The corresponding exact commuting square for right-factor tags. -/
theorem taggedTailsEquiv_rightTag
    (l : L ≃ L') (r : R ≃ R')
    (u : P ⊕ R) :
    taggedTailsEquiv l r (TaggedAmalgam.rightTag u) =
      TaggedAmalgam.rightTag (factorTailEquiv r u) := by
  cases u with
  | inl p => rfl
  | inr v => rfl

/-- If the two factor graphs have been transported along the
base-fixing tail equivalences as INDUCED graphs, the corresponding
tagged free graphs are induced-isomorphic through the natural tagged
carrier equivalence. Every positive and negative edge incidence
is reflected, and no extra compatibility hypothesis is needed
for the common base beyond the two full factor equivalences. -/
theorem taggedFreeGraph_equiv_iff
    (G : GraphOn (P ⊕ L)) (H : GraphOn (P ⊕ R))
    (G' : GraphOn (P ⊕ L')) (H' : GraphOn (P ⊕ R'))
    (l : L ≃ L') (r : R ≃ R')
    (hLeft : ∀ u v : P ⊕ L,
      G.adj u v ↔ G'.adj (factorTailEquiv l u) (factorTailEquiv l v))
    (hRight : ∀ u v : P ⊕ R,
      H.adj u v ↔ H'.adj (factorTailEquiv r u) (factorTailEquiv r v))
    (x y : TaggedAmalgam.Carrier P L R) :
    (TaggedAmalgam.freeGraph G H).adj x y ↔
      (TaggedAmalgam.freeGraph G' H').adj
        (taggedTailsEquiv l r x) (taggedTailsEquiv l r y) := by
  let EL : (P ⊕ L) ≃ (P ⊕ L') := factorTailEquiv l
  let ER : (P ⊕ R) ≃ (P ⊕ R') := factorTailEquiv r
  let E : TaggedAmalgam.Carrier P L R ≃
      TaggedAmalgam.Carrier P L' R' := taggedTailsEquiv l r
  have hTagL (u : P ⊕ L) :
      E (TaggedAmalgam.leftTag u) =
        TaggedAmalgam.leftTag (EL u) :=
    taggedTailsEquiv_leftTag l r u
  have hTagR (u : P ⊕ R) :
      E (TaggedAmalgam.rightTag u) =
        TaggedAmalgam.rightTag (ER u) :=
    taggedTailsEquiv_rightTag l r u
  constructor
  · intro h
    rcases h with ⟨u,v,hu,hv,hAdj⟩ | ⟨u,v,hu,hv,hAdj⟩
    · left
      refine ⟨EL u, EL v, ?_, ?_, (hLeft u v).mp hAdj⟩
      · exact (hTagL u).symm.trans (congrArg E hu)
      · exact (hTagL v).symm.trans (congrArg E hv)
    · right
      refine ⟨ER u, ER v, ?_, ?_, (hRight u v).mp hAdj⟩
      · exact (hTagR u).symm.trans (congrArg E hu)
      · exact (hTagR v).symm.trans (congrArg E hv)
  · intro h
    rcases h with ⟨u',v',hu',hv',hAdj'⟩ | ⟨u',v',hu',hv',hAdj'⟩
    · let u : P ⊕ L := EL.symm u'
      let v : P ⊕ L := EL.symm v'
      have hu : TaggedAmalgam.leftTag u = x := by
        apply E.injective
        calc
          E (TaggedAmalgam.leftTag u) =
              TaggedAmalgam.leftTag (EL u) := hTagL u
          _ = TaggedAmalgam.leftTag u' := by simp [u]
          _ = E x := hu'
      have hv : TaggedAmalgam.leftTag v = y := by
        apply E.injective
        calc
          E (TaggedAmalgam.leftTag v) =
              TaggedAmalgam.leftTag (EL v) := hTagL v
          _ = TaggedAmalgam.leftTag v' := by simp [v]
          _ = E y := hv'
      have hAdj : G.adj u v := (hLeft u v).mpr (by
        simpa [u, v, EL] using hAdj')
      exact Or.inl ⟨u,v,hu,hv,hAdj⟩
    · let u : P ⊕ R := ER.symm u'
      let v : P ⊕ R := ER.symm v'
      have hu : TaggedAmalgam.rightTag u = x := by
        apply E.injective
        calc
          E (TaggedAmalgam.rightTag u) =
              TaggedAmalgam.rightTag (ER u) := hTagR u
          _ = TaggedAmalgam.rightTag u' := by simp [u]
          _ = E x := hu'
      have hv : TaggedAmalgam.rightTag v = y := by
        apply E.injective
        calc
          E (TaggedAmalgam.rightTag v) =
              TaggedAmalgam.rightTag (ER v) := hTagR v
          _ = TaggedAmalgam.rightTag v' := by simp [v]
          _ = E y := hv'
      have hAdj : H.adj u v := (hRight u v).mpr (by
        simpa [u, v, ER] using hAdj')
      exact Or.inr ⟨u,v,hu,hv,hAdj⟩

end FiniteSetUnion
end BigHrushovski
