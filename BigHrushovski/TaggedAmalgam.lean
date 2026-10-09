import BigHrushovski.FreeJoinConstruction

/-!
# A fresh tagged carrier for an abstract free graph amalgam

Suppose two graph structures are presented on P ⊕ L and P ⊕ R, sharing
the P part. We construct their free amalgam on P ⊕ (L ⊕ R).
The two embeddings are injective and meet exactly on P. The graph of
the amalgam preserves both input adjacency relations, assuming that
they agree on the shared P part, and has no edges between L and R.

No finiteness assumption is needed for this relational construction.
For the full strong Fraisse theorem, one must subsequently prove that
the canonical embeddings are strong for 2-sparse finite input graphs.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}

/-- The carrier identifies P and keeps the two tails disjoint. -/
abbrev Carrier (P L R : Type*) := Sum P (Sum L R)

/-- Inclusion of the left graph on P ⊕ L. -/
def leftTag : Sum P L → Carrier P L R
  | Sum.inl p => Sum.inl p
  | Sum.inr l => Sum.inr (Sum.inl l)

/-- Inclusion of the right graph on P ⊕ R. -/
def rightTag : Sum P R → Carrier P L R
  | Sum.inl p => Sum.inl p
  | Sum.inr r => Sum.inr (Sum.inr r)

theorem leftTag_injective : Function.Injective
    (leftTag : Sum P L → Carrier P L R) := by
  intro x y h
  cases x <;> cases y <;> simp_all [leftTag]

theorem rightTag_injective : Function.Injective
    (rightTag : Sum P R → Carrier P L R) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightTag]

/-- The two inclusions identify exactly the shared base. -/
theorem leftTag_eq_rightTag {x : Sum P L} {y : Sum P R}
    (h : (leftTag x : Carrier P L R) = rightTag y) :
    ∃ p : P, x = Sum.inl p ∧ y = Sum.inl p := by
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          have hpq : p = q := by
            simpa [leftTag, rightTag] using h
          subst q
          exact ⟨p, rfl, rfl⟩
      | inr r =>
          simp [leftTag, rightTag] at h
  | inr l =>
      cases y with
      | inl p =>
          simp [leftTag, rightTag] at h
      | inr r =>
          simp [leftTag, rightTag] at h

/-- Two input graphs agree on the canonical common base. -/
def AgreeBase (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R)) : Prop :=
  ∀ p q : P, G.adj (Sum.inl p) (Sum.inl q) ↔
    H.adj (Sum.inl p) (Sum.inl q)

/-- The actual free graph on the tagged disjoint union with base identified. -/
def freeGraph (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R)) :
    GraphOn (Carrier P L R) where
  adj x y :=
    (∃ u v : Sum P L, leftTag u = x ∧ leftTag v = y ∧ G.adj u v) ∨
    (∃ u v : Sum P R, rightTag u = x ∧ rightTag v = y ∧ H.adj u v)
  symm := by
    intro x y h
    rcases h with ⟨u, v, hu, hv, hadj⟩ | ⟨u, v, hu, hv, hadj⟩
    · exact Or.inl ⟨v, u, hv, hu, G.symm u v hadj⟩
    · exact Or.inr ⟨v, u, hv, hu, H.symm u v hadj⟩
  irrefl := by
    intro x h
    rcases h with ⟨u, v, hu, hv, hadj⟩ | ⟨u, v, hu, hv, hadj⟩
    · have huv : u = v := leftTag_injective (hu.trans hv.symm)
      subst v
      exact G.irrefl u hadj
    · have huv : u = v := rightTag_injective (hu.trans hv.symm)
      subst v
      exact H.irrefl u hadj

/-- The canonical left inclusion is an induced graph embedding. -/
theorem freeGraph_left (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H) (x y : Sum P L) :
    (freeGraph G H).adj
        (leftTag x : Carrier P L R) (leftTag y) ↔ G.adj x y := by
  constructor
  · intro h
    rcases h with ⟨u, v, hu, hv, hadj⟩ |
      ⟨u, v, hu, hv, hadj⟩
    · have hux : u = x := leftTag_injective hu
      have hvy : v = y := leftTag_injective hv
      subst u
      subst v
      exact hadj
    · obtain ⟨p, hxp, hup⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hu.symm
      obtain ⟨q, hyq, hvq⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hv.symm
      subst x
      subst y
      subst u
      subst v
      exact (hAgree p q).mpr hadj
  · intro hadj
    exact Or.inl ⟨x, y, rfl, rfl, hadj⟩

/-- The canonical right inclusion is an induced graph embedding. -/
theorem freeGraph_right (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H) (x y : Sum P R) :
    (freeGraph G H).adj
        (rightTag x : Carrier P L R) (rightTag y) ↔ H.adj x y := by
  constructor
  · intro h
    rcases h with ⟨u, v, hu, hv, hadj⟩ |
      ⟨u, v, hu, hv, hadj⟩
    · obtain ⟨p, hUp, hXp⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hu
      obtain ⟨q, hVq, hYq⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hv
      subst u
      subst v
      subst x
      subst y
      exact (hAgree p q).mp hadj
    · have hux : u = x := rightTag_injective hu
      have hvy : v = y := rightTag_injective hv
      subst u
      subst v
      exact hadj
  · intro hadj
    exact Or.inr ⟨x, y, rfl, rfl, hadj⟩

/-- No new edge connects a fresh left-tail vertex to a fresh right-tail
vertex. The tags avoid all accidental identifications. -/
theorem freeGraph_no_cross (G : GraphOn (Sum P L))
    (H : GraphOn (Sum P R)) (l : L) (r : R) :
    ¬ (freeGraph G H).adj
        (Sum.inr (Sum.inl l) : Carrier P L R)
        (Sum.inr (Sum.inr r)) := by
  intro h
  rcases h with ⟨u, v, hu, hv, hadj⟩ |
    ⟨u, v, hu, hv, hadj⟩
  · cases v with
    | inl p => simp [leftTag] at hv
    | inr t => simp [leftTag] at hv
  · cases u with
    | inl p => simp [rightTag] at hu
    | inr t => simp [rightTag] at hu

/-- The fresh carrier construction simultaneously gives induced
embeddings of both input graphs, with no edges between fresh tails. -/
theorem freeGraph_amalgam (G : GraphOn (Sum P L))
    (H : GraphOn (Sum P R)) (hAgree : AgreeBase G H) :
    (∀ x y : Sum P L,
      (freeGraph G H).adj (leftTag x : Carrier P L R) (leftTag y) ↔
        G.adj x y) ∧
    (∀ x y : Sum P R,
      (freeGraph G H).adj (rightTag x : Carrier P L R) (rightTag y) ↔
        H.adj x y) ∧
    (∀ l : L, ∀ r : R,
      ¬ (freeGraph G H).adj
        (Sum.inr (Sum.inl l) : Carrier P L R)
        (Sum.inr (Sum.inr r))) := by
  exact ⟨freeGraph_left G H hAgree, freeGraph_right G H hAgree,
    freeGraph_no_cross G H⟩

end TaggedAmalgam
end BigHrushovski
