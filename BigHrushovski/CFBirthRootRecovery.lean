import BigHrushovski.CFBirthLocalRoots

/-!
# Recover the full finite b-closure from its birth-block roots

Let S be a finite subset of the actual C_F birth graph closed under
the auxiliary set-valued unary operation b(v)=P_B ∪ B. Write R(S)
for the first vertex of every birth block meeting S.

We prove that the least globally strictly d-closed hull of R(S)
equals S. The upper inclusion follows because S is globally
d-closed. For the reverse inclusion, induct on birth level.
The old named support of a block is born at earlier levels and
therefore already recovered. Its first vertex belongs to R(S).
The literal local minimal strict d-closed extension then forces
the entire block into the global hull, by the common finite
minimal-root lemma.

The special case S=C(v), the least finite b-closed superset of v,
is exactly the manuscript's first equation H(R(v))=C(v).

This module does not prove that (R,H)-embeddings and b-embeddings
have identical domains and preserve all complete function values.
Those assertions remain distinct obligations.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- A selected fresh vertex forces the *literal old support*
of that request into a finite b-closed subset of the birth graph. -/
theorem birthSupport_subset_closed_of_fresh
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hFresh : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    birthSupport F K n r ⊆ s := by
  classical
  intro v hv
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
  obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
  have hSupport : toVertex F K n u ∈ s :=
    (hs n r i hFresh).2 u hu
  have hId : v = toVertex F K n u := by
    calc
      v = toVertex F K (n + 1) w := hwv.symm
      _ = toVertex F K (n + 1) (Sum.inl u) := by rw [huw]
      _ = toVertex F K n u := toVertex_old F K n u
  rw [hId]
  exact hSupport

/-- Every ordinal of an actual request is in its own fresh block,
and consequently in the complete local finite interval. -/
theorem birthFresh_mem_block
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val) :
    (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ birthBlock F K n r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Sum.inr ⟨r, i⟩, ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- A block's first vertex is genuinely new: it is not one
of the earlier vertices belonging to the literal old support. -/
theorem birthRoot_not_support
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    birthRoot F K n r ∉ birthSupport F K n r := by
  intro hRoot
  have hLt : (birthRoot F K n r).1 < n :=
    birthSupport_birth_lt F K n r hRoot
  change n < n at hLt
  exact (Nat.lt_irrefl n) hLt

/-- Recover every vertex of any finite b-closed set from exactly
the first vertices of the birth blocks that the set meets.

The ambient hull is globally strictly d-closed in the actual
countable birth-labelled graph, not a hull in a chosen stage. -/
theorem birthDClosedHull_rootsOf_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) :
    birthDClosedHull F K (rootsOf F K s) = s := by
  classical
  let d := (countableGraph F K).toPredimension
  let roots := rootsOf F K s
  let x := birthDClosedHull F K roots
  have hRootsS : roots ⊆ s :=
    rootsOf_subset_closed F K s hs
  have hSGlobal : d.IsGloballyDClosed s :=
    birthBlockClosed_global_dClosed F K s hs
  have hxS : x ⊆ s :=
    d.globalDClosedHull_least (birthDClosedChain F K)
      hRootsS hSGlobal
  have hRootsX : roots ⊆ x :=
    d.subset_globalDClosedHull (birthDClosedChain F K) roots
  have hxGlobal : d.IsGloballyDClosed x :=
    birthDClosedHull_global F K roots
  have hByLevel : ∀ n : ℕ, ∀ v : Vertex F K,
      v.1 = n → v ∈ s → v ∈ x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v hvLevel hvS
        rcases v with ⟨m, ⟨r, i⟩⟩
        change m = n at hvLevel
        subst m
        have hSupportS : birthSupport F K n r ⊆ s :=
          birthSupport_subset_closed_of_fresh F K s hs n r i hvS
        have hSupportX : birthSupport F K n r ⊆ x := by
          intro w hw
          have hwLt : w.1 < n :=
            birthSupport_birth_lt F K n r hw
          exact ih w.1 hwLt w rfl (hSupportS hw)
        have hRootInRoots : birthRoot F K n r ∈ roots := by
          apply Finset.mem_image.mpr
          exact ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hvS, rfl⟩
        have hRootX : birthRoot F K n r ∈ x :=
          hRootsX hRootInRoots
        let P := birthSupport F K n r
        let B := birthBlock F K n r
        let L := birthLocal F K n r
        have hMinimal : d.IsMinimalDClosedStep P L :=
          birthLocal_minimal F K n r
        have hRel : d.IsDClosed x (x ∪ L) :=
          Predimension.IsGloballyDClosed.restrict d
            hxGlobal Finset.subset_union_left
        have hRootL : birthRoot F K n r ∈ L :=
          (birthBlock_subset_local F K n r)
            (birthRoot_mem_block F K n r)
        have hRootNotP : birthRoot F K n r ∉ P :=
          birthRoot_not_support F K n r
        have hAllLocal : L ⊆ x :=
          d.minimalDClosedStep_forced_by_root
            hMinimal Finset.subset_union_right hRel
            hSupportX (birthRoot F K n r)
            hRootL hRootNotP hRootX
        have hvBlock : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ B :=
          birthFresh_mem_block F K n r i
        exact hAllLocal ((birthBlock_subset_local F K n r) hvBlock)
  have hSx : s ⊆ x := by
    intro v hv
    exact hByLevel v.1 v rfl hv
  exact le_antisymm hxS hSx

/-- Least finite b-closed superset of a finite generating set,
with the same global leastness as the manuscript's iterated
component-support operation. -/
noncomputable def birthGeneratedClosure
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Finset (Vertex F K) :=
  Classical.choose (exists_least_finite_birthBlockClosure F K s)

theorem birthGeneratedClosure_contains
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    s ⊆ birthGeneratedClosure F K s :=
  (Classical.choose_spec
    (exists_least_finite_birthBlockClosure F K s)).1

theorem birthGeneratedClosure_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    IsBirthBlockClosed F K (birthGeneratedClosure F K s) :=
  (Classical.choose_spec
    (exists_least_finite_birthBlockClosure F K s)).2.1

/-- The reachable block roots of v, defined from the full
finite b-closure of v, in the precise first-ordinal presentation. -/
noncomputable def birthReachableRoots
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) : Finset (Vertex F K) :=
  rootsOf F K (birthGeneratedClosure F K ({v} : Finset (Vertex F K)))

/-- The full closure-recovery equation on the actual countable
birth graph: H(R(v)) = C(v), where H is the least globally
d-closed hull and C(v) is the generated b-closure of v. -/
theorem birthRoot_recovery
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) :
    birthDClosedHull F K (birthReachableRoots F K v) =
      birthGeneratedClosure F K ({v} : Finset (Vertex F K)) :=
  birthDClosedHull_rootsOf_closed F K _
    (birthGeneratedClosure_closed F K ({v} : Finset (Vertex F K)))

end CFCoherentTower
end BigHrushovski
