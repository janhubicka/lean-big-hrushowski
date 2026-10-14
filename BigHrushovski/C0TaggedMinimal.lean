import BigHrushovski.C0OneBlockResponse
import BigHrushovski.TaggedStrongAmalgam

/-!
# One minimal strong component in a tagged free graph amalgam

We identify the common closed base P and keep old and new tails tagged,
with finite carrier P ⊕ (L ⊕ R). The old graph G is on P ⊕ L and the
local new component H is on P ⊕ R.

If the two graph structures agree on P, P is strong in G, and P < H
is a minimal strong step, the free graph amalgam is 2-sparse and its
extension of the whole old left factor by R is again minimal strong.

This supplies the missing construction of the finite graph input K
for the already certified labelled minimal response theorem.
It does not construct the countable functional scheduling recursion.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]

/-- The genuinely fresh right tail of the amalgam, computed from
the canonical factor domains rather than from a chosen enumeration. -/
noncomputable def rightTail : Finset (Carrier P L R) :=
  rightDomain \ leftDomain

/-- The local right factor is precisely the shared base plus its
fresh right tail. -/
theorem rightDomain_eq_base_union_tail :
    baseDomain ∪ (rightTail : Finset (Carrier P L R)) =
      rightDomain := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxBase | hxTail
    · have hInter : x ∈ (leftDomain : Finset (Carrier P L R)) ∩
          rightDomain := by
        rw [domains_inter_eq_base]
        exact hxBase
      exact (Finset.mem_inter.mp hInter).2
    · exact (Finset.mem_sdiff.mp hxTail).1
  · intro hxRight
    by_cases hxLeft : x ∈ (leftDomain : Finset (Carrier P L R))
    · apply Finset.mem_union.mpr
      left
      have hInter : x ∈ (leftDomain : Finset (Carrier P L R)) ∩
          rightDomain := Finset.mem_inter.mpr ⟨hxLeft, hxRight⟩
      rw [domains_inter_eq_base] at hInter
      exact hInter
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_sdiff.mpr ⟨hxRight, hxLeft⟩))

/-- The old left domain together with exactly the fresh right vertices
covers the whole tagged carrier, with no repeated vertices. -/
theorem leftDomain_union_tail_univ :
    (leftDomain : Finset (Carrier P L R)) ∪ rightTail =
      Finset.univ := by
  classical
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    have hx : x ∈ (leftDomain : Finset (Carrier P L R)) ∪
        rightDomain := by
      rw [domains_union_univ]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hxLeft | hxRight
    · exact Finset.mem_union.mpr (Or.inl hxLeft)
    · by_cases hxLeft : x ∈ (leftDomain : Finset (Carrier P L R))
      · exact Finset.mem_union.mpr (Or.inl hxLeft)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_sdiff.mpr ⟨hxRight, hxLeft⟩))

/-- The fresh right tail is disjoint from the whole old graph. -/
theorem leftDomain_disjoint_rightTail :
    Disjoint (leftDomain : Finset (Carrier P L R)) rightTail := by
  apply Finset.disjoint_left.mpr
  intro x hxLeft hxTail
  exact (Finset.mem_sdiff.mp hxTail).2 hxLeft

/-- The tagged free-graph construction retains the minimality of the
local P < P∪R step after adding the old left vertices L. -/
theorem tagged_freeGraph_minimal_left_extension
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (hMinimal : H.toPredimension.IsMinimalStrongStep rightBase
      (Finset.univ : Finset (Sum P R))) :
    (freeGraph G H).toPredimension.IsMinimalStrongStep
      leftDomain (Finset.univ : Finset (Carrier P L R)) := by
  classical
  let F := freeGraph G H
  have hRightAdj : ∀ x y : Sum P R,
      H.adj x y ↔ F.adj (rightTag x) (rightTag y) :=
    fun x y => (freeGraph_right G H hAgree x y).symm
  have hLocal :
      F.toPredimension.IsMinimalStrongStep
        baseDomain rightDomain := by
    have h := (H.minimalStrongStep_image_iff F
      (rightTag : Sum P R → Carrier P L R)
      rightTag_injective hRightAdj rightBase
      (Finset.univ : Finset (Sum P R))
      (Finset.subset_univ _)).mpr hMinimal
    change F.toPredimension.IsMinimalStrongStep
      ((rightBase : Finset (Sum P R)).image rightTag)
      rightDomain at h
    rw [rightBase_image_eq_base] at h
    exact h
  have hBaseSub : (baseDomain : Finset (Carrier P L R)) ⊆
      leftDomain := by
    intro x hx
    have hInter : x ∈ (leftDomain : Finset (Carrier P L R)) ∩
        rightDomain := by
      rw [domains_inter_eq_base]
      exact hx
    exact (Finset.mem_inter.mp hInter).1
  have hNo : F.NoCrossEdges leftDomain
      (baseDomain ∪ rightTail) := by
    rw [rightDomain_eq_base_union_tail]
    exact tagged_freeGraph_noCross G H
  have hLocal' :
      F.toPredimension.IsMinimalStrongStep
        baseDomain (baseDomain ∪ rightTail) := by
    rw [rightDomain_eq_base_union_tail]
    exact hLocal
  have hLift : F.toPredimension.IsMinimalStrongStep
      leftDomain (leftDomain ∪ rightTail) :=
    F.minimalStrongStep_enlarged_of_local
      baseDomain leftDomain rightTail hBaseSub
      leftDomain_disjoint_rightTail hNo hLocal'
  rw [leftDomain_union_tail_univ] at hLift
  exact hLift

/-- A finite minimal strong component attached freely over a strong
common base gives an actual 2-sparse free graph amalgam in which the
entire old factor embeds as a minimal strong substructure. -/
theorem tagged_minimal_strong_free_amalgam
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (hSparseG : G.IsTwoSparse
      (Finset.univ : Finset (Sum P L)))
    (hSparseH : H.IsTwoSparse
      (Finset.univ : Finset (Sum P R)))
    (hBaseG : G.toPredimension.IsStrong leftBase
      (Finset.univ : Finset (Sum P L)))
    (hMinimalH : H.toPredimension.IsMinimalStrongStep rightBase
      (Finset.univ : Finset (Sum P R))) :
    (freeGraph G H).IsTwoSparse
      (Finset.univ : Finset (Carrier P L R)) ∧
    (freeGraph G H).toPredimension.IsMinimalStrongStep
      leftDomain (Finset.univ : Finset (Carrier P L R)) ∧
    (∀ x y : Sum P L, (freeGraph G H).adj
      (leftTag x) (leftTag y) ↔ G.adj x y) ∧
    (∀ x y : Sum P R, (freeGraph G H).adj
      (rightTag x) (rightTag y) ↔ H.adj x y) := by
  have hAmalgam := tagged_strong_free_amalgam G H hAgree
    hSparseG hSparseH hBaseG hMinimalH.1
  exact ⟨hAmalgam.1,
    tagged_freeGraph_minimal_left_extension G H hAgree hMinimalH,
    freeGraph_left G H hAgree,
    freeGraph_right G H hAgree⟩

end TaggedAmalgam
end BigHrushovski
