import BigHrushovski.CFBirthRootRecovery

/-!
# The same closed substructures in the b and (R,H) presentations

The auxiliary b-operation attaches the complete fresh request block
and its old named support. The alternative presentation records the
first vertices of all blocks in the finite b-closure of a vertex,
together with the *partial* global d-closed hull H of finite sets
consisting exclusively of first vertices.

We prove the equality of closed *vertex subsets*, without assuming
they are finite. The finite-cut argument is essential: any finite
set contained in a possibly infinite b-closed subset lies in its
intersection with a sufficiently large finite stage, which is a
finite b-closed set. Its generated b-closure and its global d-hull
therefore remain in the possibly infinite subset.

This does not identify embeddings: for that one must additionally
show that induced maps carry complete finite function values and
reflect the domain of the partial operation H.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Closure under complete b-values, for an arbitrary vertex subset.
Unlike IsBirthBlockClosed on Finset, no finiteness is required. -/
def IsBirthBlockClosedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) : Prop :=
  ∀ (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val),
    (⟨n, ⟨r,i⟩⟩ : Vertex F K) ∈ X →
      (∀ j : Fin r.code.1.val,
        (⟨n, ⟨r,j⟩⟩ : Vertex F K) ∈ X) ∧
      (∀ u ∈ r.support, toVertex F K n u ∈ X)

/-- The globally recognizable first vertices, those fixed by rootOf.
This avoids declaring H on arbitrary finite vertex sets in the
functional language. -/
def IsBirthRoot (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) : Prop :=
  rootOf F K v = v

/-- R-closure together with all *defined* H-values on finite sets
of birth roots. The source and image tests use ordinary sets and
therefore include infinite closed subsets. -/
def IsRHClosedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) : Prop :=
  (∀ v ∈ X, ∀ r ∈ birthReachableRoots F K v, r ∈ X) ∧
  (∀ s : Finset (Vertex F K),
    (∀ r ∈ s, IsBirthRoot F K r) →
    (∀ r ∈ s, r ∈ X) →
    ∀ v ∈ birthDClosedHull F K s, v ∈ X)

/-- Every chosen root is a root, also for a vertex with a nonzero
fresh ordinal. This is a literal property of birth tags. -/
theorem rootOf_idempotent
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K) :
    rootOf F K (rootOf F K v) = rootOf F K v := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  rfl

/-- All members of R(v) are actual birth roots, not arbitrary
vertices of its d-closure. -/
theorem reachableRoots_are_roots
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K) :
    ∀ r ∈ birthReachableRoots F K v, IsBirthRoot F K r := by
  intro r hr
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hr
  rw [← hw]
  exact rootOf_idempotent F K w

/-- The finite part of an arbitrary vertex subset lying in one
birth stage. Classical membership decisions are confined here;
the closure assertions themselves are propositions. -/
noncomputable def stageSetCut
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) (n : ℕ) : Finset (Vertex F K) := by
  classical
  exact (stageImage F K n).filter (fun v => v ∈ X)

/-- The intersection of an arbitrary b-closed set with the finite
birth stage is b-closed as a Finset. All whole blocks and old
supports remain in the stage because dependencies go backwards. -/
theorem stageCut_closedSet_bClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X) (n : ℕ) :
    IsBirthBlockClosed F K
      (stageSetCut F K X n) := by
  classical
  intro m r i hi
  obtain ⟨hStage, hInX⟩ := Finset.mem_filter.mp hi
  have hm : m < n :=
    (mem_stageImage_iff_birth_lt F K n _).mp hStage
  obtain ⟨hBlock, hSupport⟩ := hX m r i hInX
  constructor
  · intro j
    apply Finset.mem_filter.mpr
    exact ⟨(mem_stageImage_iff_birth_lt F K n _).mpr hm,
      hBlock j⟩
  · intro u hu
    apply Finset.mem_filter.mpr
    have hBefore : (toVertex F K m u).1 < m :=
      toVertex_birth_lt F K m u
    exact ⟨(mem_stageImage_iff_birth_lt F K n _).mpr
      (hBefore.trans hm), hSupport u hu⟩

/-- Every finite set inside an arbitrary (possibly infinite)
b-closed set has its finite generated b-closure inside that set. -/
theorem generatedClosure_subset_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (s : Finset (Vertex F K))
    (hsX : ∀ v ∈ s, v ∈ X) :
    ∀ v ∈ birthGeneratedClosure F K s, v ∈ X := by
  classical
  obtain ⟨n, hsStage⟩ := finiteSet_covered F K s
  let t : Finset (Vertex F K) := stageSetCut F K X n
  have htClosed : IsBirthBlockClosed F K t :=
    stageCut_closedSet_bClosed F K X hX n
  have hst : s ⊆ t := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨hsStage hv, hsX v hv⟩
  have hLeast :
      birthGeneratedClosure F K s ⊆ t :=
    (Classical.choose_spec
      (exists_least_finite_birthBlockClosure F K s)).2.2
      t hst htClosed
  intro v hv
  exact (Finset.mem_filter.mp (hLeast hv)).2

/-- A finite set of vertices inside a b-closed (possibly infinite)
subset has its entire globally d-closed hull in that subset.
This is stronger than needed for H, whose domain consists of roots. -/
theorem birthHull_subset_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (s : Finset (Vertex F K))
    (hsX : ∀ v ∈ s, v ∈ X) :
    ∀ v ∈ birthDClosedHull F K s, v ∈ X := by
  let c := birthGeneratedClosure F K s
  have hSc : s ⊆ c :=
    birthGeneratedClosure_contains F K s
  have hcClosed : IsBirthBlockClosed F K c :=
    birthGeneratedClosure_closed F K s
  have hcGlobal := birthBlockClosed_global_dClosed F K c hcClosed
  have hHull : birthDClosedHull F K s ⊆ c :=
    (countableGraph F K).toPredimension.globalDClosedHull_least
      (birthDClosedChain F K) hSc hcGlobal
  have hcX : ∀ v ∈ c, v ∈ X :=
    generatedClosure_subset_closedSet F K X hX s hsX
  intro v hv
  exact hcX v (hHull hv)

/-- Every b-closed subset, finite or infinite, is closed under
all R(v)-values and every defined H-value on finite root sets. -/
theorem rhClosed_of_birthBlockClosedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X) :
    IsRHClosedSet F K X := by
  constructor
  · intro v hv r hr
    have hG : ∀ w ∈ birthGeneratedClosure F K ({v} : Finset (Vertex F K)), w ∈ X :=
      generatedClosure_subset_closedSet F K X hX ({v}) (by
        intro u hu
        have huv : u = v := by simpa using hu
        subst u
        exact hv)
    have hrC : r ∈ birthGeneratedClosure F K ({v} : Finset (Vertex F K)) :=
      rootsOf_subset_closed F K _
        (birthGeneratedClosure_closed F K ({v})) hr
    exact hG r hrC
  · intro s hRoots hs v hv
    exact birthHull_subset_closedSet F K X hX s hs v hv

/-- Closing under R and permitted H-values already forces
every complete b-value. The recovered equation H(R(v))=C(v)
is used in precisely the direction needed. -/
theorem birthBlockClosedSet_of_rhClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsRHClosedSet F K X) :
    IsBirthBlockClosedSet F K X := by
  intro n r i hVertex
  let v : Vertex F K := ⟨n, ⟨r, i⟩⟩
  let C := birthGeneratedClosure F K ({v} : Finset (Vertex F K))
  have hRootsX : ∀ t ∈ birthReachableRoots F K v, t ∈ X :=
    hX.1 v hVertex
  have hRootsAre : ∀ t ∈ birthReachableRoots F K v,
      IsBirthRoot F K t :=
    reachableRoots_are_roots F K v
  have hCX : ∀ t ∈ C, t ∈ X := by
    intro t ht
    have htHull : t ∈ birthDClosedHull F K (birthReachableRoots F K v) := by
      rw [birthRoot_recovery F K v]
      exact ht
    exact hX.2 (birthReachableRoots F K v)
      hRootsAre hRootsX t htHull
  have hInC : v ∈ C :=
    (birthGeneratedClosure_contains F K ({v}))
      (Finset.mem_singleton_self v)
  obtain ⟨hAll, hSupp⟩ :=
    (birthGeneratedClosure_closed F K ({v})) n r i hInC
  constructor
  · intro j
    exact hCX _ (hAll j)
  · intro u hu
    exact hCX _ (hSupp u hu)

/-- The two presentations have exactly the same substructures,
with their full closure values, on *arbitrary* vertex subsets.
In particular the assertion applies to infinite subsets without
ever defining predimension on them. -/
theorem birthBlockClosedSet_iff_rhClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) :
    IsBirthBlockClosedSet F K X ↔ IsRHClosedSet F K X := by
  constructor
  · exact rhClosed_of_birthBlockClosedSet F K X
  · exact birthBlockClosedSet_of_rhClosed F K X

end CFCoherentTower
end BigHrushovski
