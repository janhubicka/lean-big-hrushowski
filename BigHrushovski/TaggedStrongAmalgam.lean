import BigHrushovski.InducedEmbedding

/-!
# The finite domains of the tagged free graph amalgam

The carrier is P ⊕ (L ⊕ R). Its canonical induced left and right
domains intersect exactly on P, cover the carrier, and have no
crossing edges. These are the carrier facts needed to apply the
already verified free-join predimension and strongness lemmas.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]

noncomputable def leftDomain : Finset (Carrier P L R) :=
  (Finset.univ : Finset (Sum P L)).image
    (leftTag : Sum P L → Carrier P L R)

noncomputable def rightDomain : Finset (Carrier P L R) :=
  (Finset.univ : Finset (Sum P R)).image
    (rightTag : Sum P R → Carrier P L R)

noncomputable def baseDomain : Finset (Carrier P L R) :=
  (Finset.univ : Finset P).image
    (Sum.inl : P → Carrier P L R)

noncomputable def leftBase : Finset (Sum P L) :=
  (Finset.univ : Finset P).image (Sum.inl : P → Sum P L)

noncomputable def rightBase : Finset (Sum P R) :=
  (Finset.univ : Finset P).image (Sum.inl : P → Sum P R)

theorem leftTag_mem_domain (u : Sum P L) :
    (leftTag u : Carrier P L R) ∈ (leftDomain : Finset (Carrier P L R)) := by
  classical
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

theorem rightTag_mem_domain (u : Sum P R) :
    (rightTag u : Carrier P L R) ∈ (rightDomain : Finset (Carrier P L R)) := by
  classical
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

/-- The images of the two factors have exactly their P-part in common. -/
theorem domains_inter_eq_base :
    (leftDomain : Finset (Carrier P L R)) ∩ rightDomain =
      baseDomain := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, _, hu⟩ :=
      Finset.mem_image.mp (Finset.mem_inter.mp hx).1
    obtain ⟨v, _, hv⟩ :=
      Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    obtain ⟨p, hpU, hpV⟩ :=
      leftTag_eq_rightTag (P := P) (L := L) (R := R)
        (hu.trans hv.symm)
    subst u
    exact Finset.mem_image.mpr
      ⟨p, Finset.mem_univ _, by simpa [leftTag] using hu⟩
  · intro hx
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hx
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr
        ⟨Sum.inl p, Finset.mem_univ _, by simpa [leftTag] using hp⟩
    · exact Finset.mem_image.mpr
        ⟨Sum.inl p, Finset.mem_univ _, by simpa [rightTag] using hp⟩

theorem leftBase_image_eq_base :
    (leftBase : Finset (Sum P L)).image
      (leftTag : Sum P L → Carrier P L R) = baseDomain := by
  classical
  unfold leftBase baseDomain
  rw [Finset.image_image]
  have hFun : (leftTag : Sum P L → Carrier P L R) ∘ Sum.inl =
      (Sum.inl : P → Carrier P L R) := by
    funext p
    rfl
  rw [hFun]

theorem rightBase_image_eq_base :
    (rightBase : Finset (Sum P R)).image
      (rightTag : Sum P R → Carrier P L R) = baseDomain := by
  classical
  unfold rightBase baseDomain
  rw [Finset.image_image]
  have hFun : (rightTag : Sum P R → Carrier P L R) ∘ Sum.inl =
      (Sum.inl : P → Carrier P L R) := by
    funext p
    rfl
  rw [hFun]

theorem domains_union_univ :
    (leftDomain : Finset (Carrier P L R)) ∪ rightDomain =
      Finset.univ := by
  classical
  ext x
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    cases x with
    | inl p =>
        exact Finset.mem_union.mpr (Or.inl
          (leftTag_mem_domain (P := P) (L := L) (R := R) (Sum.inl p)))
    | inr y =>
        cases y with
        | inl l =>
            exact Finset.mem_union.mpr (Or.inl
              (leftTag_mem_domain (P := P) (L := L) (R := R) (Sum.inr l)))
        | inr r =>
            exact Finset.mem_union.mpr (Or.inr
              (rightTag_mem_domain (P := P) (L := L) (R := R) (Sum.inr r)))

/-- Every edge of the tagged free graph belongs to an induced factor. -/
theorem tagged_freeGraph_noCross
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R)) :
    (freeGraph G H).NoCrossEdges leftDomain rightDomain := by
  classical
  let F := freeGraph G H
  intro edge he
  obtain ⟨_, hEdge⟩ :=
    (F.mem_edgesWithin_iff (leftDomain ∪ rightDomain) edge).mp he
  obtain ⟨hcard, x, hx, y, hy, hAdj⟩ := hEdge
  have hEdgeSaved : F.IsEdge edge := ⟨hcard, x, hx, y, hy, hAdj⟩
  have hne : x ≠ y := by
    intro hxy
    subst y
    exact F.irrefl x hAdj
  have hpairCard : (insert x ({y} : Finset (Carrier P L R))).card = 2 := by
    simp [hne]
  have hpairSub : insert x ({y} : Finset (Carrier P L R)) ⊆ edge := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hzy
    · subst z
      exact hx
    · have hzEq : z = y := Finset.mem_singleton.mp hzy
      subst z
      exact hy
  have heq : edge = insert x ({y} : Finset (Carrier P L R)) := by
    have h := Finset.eq_of_subset_of_card_le hpairSub (by omega)
    exact h.symm
  change (∃ u v : Sum P L, leftTag u = x ∧ leftTag v = y ∧ G.adj u v) ∨
    (∃ u v : Sum P R, rightTag u = x ∧ rightTag v = y ∧ H.adj u v)
      at hAdj
  rcases hAdj with ⟨u, v, hu, hv, _⟩ | ⟨u, v, hu, hv, _⟩
  · have hxL : x ∈ (leftDomain : Finset (Carrier P L R)) := by
      rw [← hu]
      exact leftTag_mem_domain u
    have hyL : y ∈ (leftDomain : Finset (Carrier P L R)) := by
      rw [← hv]
      exact leftTag_mem_domain v
    have hSub : edge ⊆ leftDomain := by
      rw [heq]
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hzy
      · subst z
        exact hxL
      · have hzEq : z = y := Finset.mem_singleton.mp hzy
        subst z
        exact hyL
    exact Finset.mem_union.mpr (Or.inl
      ((F.mem_edgesWithin_iff leftDomain edge).mpr ⟨hSub, hEdgeSaved⟩))
  · have hxR : x ∈ (rightDomain : Finset (Carrier P L R)) := by
      rw [← hu]
      exact rightTag_mem_domain u
    have hyR : y ∈ (rightDomain : Finset (Carrier P L R)) := by
      rw [← hv]
      exact rightTag_mem_domain v
    have hSub : edge ⊆ rightDomain := by
      rw [heq]
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hzy
      · subst z
        exact hxR
      · have hzEq : z = y := Finset.mem_singleton.mp hzy
        subst z
        exact hyR
    exact Finset.mem_union.mpr (Or.inr
      ((F.mem_edgesWithin_iff rightDomain edge).mpr ⟨hSub, hEdgeSaved⟩))

end TaggedAmalgam
end BigHrushovski
