import BigHrushovski.C0ClosedHereditary
import BigHrushovski.TaggedAmalgam

/-!
# Backward dependency closure under tagged free amalgamation

The one-generated unary closure of a C0 component is the union of the
components reachable by backwards dependencies. To preserve that
function in a free amalgam, one must preserve *all* such paths, not
merely adjacency of the underlying graphs.

This abstract finite-dependency calculation uses the existing tagged
carrier P ⊕ (L ⊕ R). The two directed dependency relations agree on the
common base, and the base has no directed dependency into either tail.
Then a dependency path starting in either input factor cannot leave
that factor. Its reflexive transitive closure in the amalgam agrees
exactly with its original reflexive transitive closure.

No predimension condition is assumed or needed here. The application
to the actual finite C0 component-language must still identify the
back-edge dependency relation and whole-component values.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}

/-- The two dependencies coincide when both vertices lie in P. -/
def DependencyAgreeBase
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop) : Prop :=
  ∀ p q : P, dL (.inl p) (.inl q) ↔ dR (.inl p) (.inl q)

/-- The base is closed under backwards dependencies in the left factor. -/
def DependencyLeftBaseClosed
    (dL : Sum P L → Sum P L → Prop) : Prop :=
  ∀ p : P, ∀ y : Sum P L, dL (.inl p) y →
    ∃ q : P, y = .inl q

/-- The base is closed under backwards dependencies in the right factor. -/
def DependencyRightBaseClosed
    (dR : Sum P R → Sum P R → Prop) : Prop :=
  ∀ p : P, ∀ y : Sum P R, dR (.inl p) y →
    ∃ q : P, y = .inl q

/-- The actual union of both dependency relations on the tagged carrier. -/
def freeDependency
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (x y : Carrier P L R) : Prop :=
  (∃ u v : Sum P L, leftTag u = x ∧ leftTag v = y ∧ dL u v) ∨
  (∃ u v : Sum P R, rightTag u = x ∧ rightTag v = y ∧ dR u v)

/-- Dependencies between two points of the left factor are unchanged. -/
theorem freeDependency_left_iff
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR) (x y : Sum P L) :
    freeDependency dL dR (leftTag x) (leftTag y) ↔ dL x y := by
  constructor
  · intro h
    rcases h with ⟨u, v, hu, hv, hdep⟩ |
      ⟨u, v, hu, hv, hdep⟩
    · have hux : u = x := leftTag_injective hu
      have hvy : v = y := leftTag_injective hv
      subst u
      subst v
      exact hdep
    · obtain ⟨p, hxp, hup⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hu.symm
      obtain ⟨q, hyq, hvq⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hv.symm
      subst x
      subst y
      subst u
      subst v
      exact (hAgree p q).mpr hdep
  · intro h
    exact Or.inl ⟨x, y, rfl, rfl, h⟩

/-- Dependencies between two points of the right factor are unchanged. -/
theorem freeDependency_right_iff
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR) (x y : Sum P R) :
    freeDependency dL dR (rightTag x) (rightTag y) ↔ dR x y := by
  constructor
  · intro h
    rcases h with ⟨u, v, hu, hv, hdep⟩ |
      ⟨u, v, hu, hv, hdep⟩
    · obtain ⟨p, hup, hxp⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hu
      obtain ⟨q, hvq, hyq⟩ :=
        leftTag_eq_rightTag (P := P) (L := L) (R := R) hv
      subst u
      subst v
      subst x
      subst y
      exact (hAgree p q).mp hdep
    · have hux : u = x := rightTag_injective hu
      have hvy : v = y := rightTag_injective hv
      subst u
      subst v
      exact hdep
  · intro h
    exact Or.inr ⟨x, y, rfl, rfl, h⟩

/-- A free dependency leaving the left factor must end in the left factor.
The only delicate case starts in the common base and is contributed by
the right relation. -/
theorem freeDependency_left_target
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hClosed : DependencyRightBaseClosed dR)
    (x : Sum P L) (z : Carrier P L R)
    (h : freeDependency dL dR (leftTag x) z) :
    ∃ y : Sum P L, z = leftTag y := by
  rcases h with ⟨u, v, _, hv, _⟩ |
    ⟨u, v, hu, hv, hdep⟩
  · exact ⟨v, hv.symm⟩
  · obtain ⟨p, _, hup⟩ :=
      leftTag_eq_rightTag (P := P) (L := L) (R := R) hu.symm
    obtain ⟨q, hvq⟩ := hClosed p v (by simpa only [hup] using hdep)
    refine ⟨Sum.inl q, ?_⟩
    simpa [leftTag, rightTag, hvq] using hv.symm

/-- A free dependency leaving the right factor must end in the right factor. -/
theorem freeDependency_right_target
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hClosed : DependencyLeftBaseClosed dL)
    (x : Sum P R) (z : Carrier P L R)
    (h : freeDependency dL dR (rightTag x) z) :
    ∃ y : Sum P R, z = rightTag y := by
  rcases h with ⟨u, v, hu, hv, hdep⟩ |
    ⟨u, v, _, hv, _⟩
  · obtain ⟨p, hup, _⟩ :=
      leftTag_eq_rightTag (P := P) (L := L) (R := R) hu
    obtain ⟨q, hvq⟩ := hClosed p v (by simpa only [hup] using hdep)
    refine ⟨Sum.inl q, ?_⟩
    simpa [leftTag, rightTag, hvq] using hv.symm
  · exact ⟨v, hv.symm⟩

/-- Reachability by zero or more directed dependencies. -/
inductive DependencyAncestor {V : Type*}
    (d : V → V → Prop) (root : V) : V → Prop where
  | root : DependencyAncestor d root root
  | step {u v : V} (hu : DependencyAncestor d root u)
      (hdep : d u v) : DependencyAncestor d root v

/-- A dependency path in the left factor is also a path in the join. -/
theorem leftAncestor_forward
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    {x y : Sum P L}
    (h : DependencyAncestor dL x y) :
    DependencyAncestor (freeDependency dL dR) (leftTag x) (leftTag y) := by
  induction h with
  | root =>
      exact DependencyAncestor.root
  | @step u v hu hdep ih =>
      exact DependencyAncestor.step ih
        (Or.inl ⟨u, v, rfl, rfl, hdep⟩)

/-- Every dependency path in the join starting on the left can be
lifted completely back to the left factor. -/
theorem leftAncestor_backward
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyRightBaseClosed dR)
    (x : Sum P L) {z : Carrier P L R}
    (h : DependencyAncestor (freeDependency dL dR) (leftTag x) z) :
    ∃ y : Sum P L, z = leftTag y ∧ DependencyAncestor dL x y := by
  induction h with
  | root =>
      exact ⟨x, rfl, DependencyAncestor.root⟩
  | @step u v hu hdep ih =>
      obtain ⟨y, hy, hAnc⟩ := ih
      rw [hy] at hdep
      obtain ⟨y', hy'⟩ :=
        freeDependency_left_target dL dR hClosed y v hdep
      refine ⟨y', hy', ?_⟩
      have hSame : freeDependency dL dR (leftTag y) (leftTag y') := by
        simpa only [hy'] using hdep
      exact DependencyAncestor.step hAnc
        ((freeDependency_left_iff dL dR hAgree y y').mp hSame)

/-- The left factor's entire backward dependency closure is unchanged
by the tagged join. The equality includes all descendants, not only
individual dependency edges. -/
theorem freeDependency_left_ancestor_iff
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyRightBaseClosed dR)
    (x : Sum P L) (z : Carrier P L R) :
    DependencyAncestor (freeDependency dL dR) (leftTag x) z ↔
      ∃ y : Sum P L, z = leftTag y ∧ DependencyAncestor dL x y := by
  constructor
  · exact leftAncestor_backward dL dR hAgree hClosed x
  · rintro ⟨y, rfl, hAnc⟩
    exact leftAncestor_forward dL dR hAnc

/-- Symmetric path preservation for the right factor. -/
theorem rightAncestor_forward
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    {x y : Sum P R}
    (h : DependencyAncestor dR x y) :
    DependencyAncestor (freeDependency dL dR) (rightTag x) (rightTag y) := by
  induction h with
  | root =>
      exact DependencyAncestor.root
  | @step u v hu hdep ih =>
      exact DependencyAncestor.step ih
        (Or.inr ⟨u, v, rfl, rfl, hdep⟩)

theorem rightAncestor_backward
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyLeftBaseClosed dL)
    (x : Sum P R) {z : Carrier P L R}
    (h : DependencyAncestor (freeDependency dL dR) (rightTag x) z) :
    ∃ y : Sum P R, z = rightTag y ∧ DependencyAncestor dR x y := by
  induction h with
  | root =>
      exact ⟨x, rfl, DependencyAncestor.root⟩
  | @step u v hu hdep ih =>
      obtain ⟨y, hy, hAnc⟩ := ih
      rw [hy] at hdep
      obtain ⟨y', hy'⟩ :=
        freeDependency_right_target dL dR hClosed y v hdep
      refine ⟨y', hy', ?_⟩
      have hSame : freeDependency dL dR (rightTag y) (rightTag y') := by
        simpa only [hy'] using hdep
      exact DependencyAncestor.step hAnc
        ((freeDependency_right_iff dL dR hAgree y y').mp hSame)

theorem freeDependency_right_ancestor_iff
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyLeftBaseClosed dL)
    (x : Sum P R) (z : Carrier P L R) :
    DependencyAncestor (freeDependency dL dR) (rightTag x) z ↔
      ∃ y : Sum P R, z = rightTag y ∧ DependencyAncestor dR x y := by
  constructor
  · exact rightAncestor_backward dL dR hAgree hClosed x
  · rintro ⟨y, rfl, hAnc⟩
    exact rightAncestor_forward dL dR hAnc

/-- Finite one-generated closure of a vertex under a dependency relation. -/
noncomputable def dependencyClosure {V : Type*} [Fintype V]
    (d : V → V → Prop) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (DependencyAncestor d x)

theorem mem_dependencyClosure_iff {V : Type*} [Fintype V]
    (d : V → V → Prop) (x y : V) :
    y ∈ dependencyClosure d x ↔ DependencyAncestor d x y := by
  classical
  simp [dependencyClosure]

/-- Exact equality of *set-valued* unary closures in the left factor.
This is the finite functional analogue of the path lemma. -/
theorem freeDependency_closure_left
    [Fintype P] [Fintype L] [Fintype R]
    [DecidableEq P] [DecidableEq L] [DecidableEq R]
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyRightBaseClosed dR)
    (x : Sum P L) :
    dependencyClosure (freeDependency dL dR) (leftTag x) =
      (dependencyClosure dL x).image
        (leftTag : Sum P L → Carrier P L R) := by
  classical
  ext z
  rw [mem_dependencyClosure_iff]
  constructor
  · intro hz
    obtain ⟨y, hzy, hy⟩ :=
      (freeDependency_left_ancestor_iff dL dR hAgree hClosed x z).mp hz
    exact Finset.mem_image.mpr
      ⟨y, (mem_dependencyClosure_iff dL x y).mpr hy, hzy.symm⟩
  · intro hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.mp hz
    have hAnc : DependencyAncestor dL x y :=
      (mem_dependencyClosure_iff dL x y).mp hy
    have hJoined := leftAncestor_forward dL dR hAnc
    rw [hzy] at hJoined
    exact hJoined

/-- Exact equality of set-valued unary closures in the right factor. -/
theorem freeDependency_closure_right
    [Fintype P] [Fintype L] [Fintype R]
    [DecidableEq P] [DecidableEq L] [DecidableEq R]
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyLeftBaseClosed dL)
    (x : Sum P R) :
    dependencyClosure (freeDependency dL dR) (rightTag x) =
      (dependencyClosure dR x).image
        (rightTag : Sum P R → Carrier P L R) := by
  classical
  ext z
  rw [mem_dependencyClosure_iff]
  constructor
  · intro hz
    obtain ⟨y, hzy, hy⟩ :=
      (freeDependency_right_ancestor_iff dL dR hAgree hClosed x z).mp hz
    exact Finset.mem_image.mpr
      ⟨y, (mem_dependencyClosure_iff dR x y).mpr hy, hzy.symm⟩
  · intro hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.mp hz
    have hAnc : DependencyAncestor dR x y :=
      (mem_dependencyClosure_iff dR x y).mp hy
    have hJoined := rightAncestor_forward dL dR hAnc
    rw [hzy] at hJoined
    exact hJoined

end TaggedAmalgam
end BigHrushovski
