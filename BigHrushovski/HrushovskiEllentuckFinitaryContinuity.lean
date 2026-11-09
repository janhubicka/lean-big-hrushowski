import BigHrushovski.HrushovskiEllentuckCFBirthTopology

/-!
# Finitary continuity of complete-support domains

If the support of each vertex is finite, then membership of finitely
many vertices in a support-saturated domain depends on finitely many
level coordinates. Moreover support-saturated domains preserve
increasing unions of level sets. The second assertion requires
monotonicity: arbitrary unions need not be preserved.

The general lemmas apply to the R₀ and R_F finite-support interfaces;
the final two theorems instantiate them on the *actual* countable C_F
birth carrier with its full generated auxiliary b-support.

Nothing here asserts that a supported domain is the range of a
self-embedding in the (R,H) functional language, that arbitrary level
maps lift, or that the concrete Section 6 Ramsey-space axioms hold.
-/

namespace BigHrushovski.Ellentuck

universe u v
variable {Level : Type u} {Vertex : Type v}

/-- The membership of a finite set of vertices in the supported domain
is decided by one finite set of levels, obtained as the union of
their *whole* supports. -/
theorem supportDomain_local_finset
    (support : Vertex → Finset Level)
    (s : Finset Vertex) :
    ∃ t : Finset Level,
      ∀ (S T : Set Level),
        (∀ q ∈ t, (q ∈ S ↔ q ∈ T)) →
        ∀ x ∈ s,
          (x ∈ supportDomain support S ↔
           x ∈ supportDomain support T) := by
  classical
  refine ⟨s.biUnion support, ?_⟩
  intro S T hST x hx
  apply supportDomain_local support S T x
  intro q hq
  exact hST q (Finset.mem_biUnion.mpr ⟨x, hx, hq⟩)

/-- A finite set contained in an increasing union is contained in a
single member of the sequence. No finite bound is assumed on the sets
forming the sequence. -/
private theorem finset_subset_iUnion_of_monotone
    {α : Type*}
    (S : ℕ → Set α) (hS : Monotone S)
    (s : Finset α)
    (hs : ∀ x ∈ s, x ∈ ⋃ n, S n) :
    ∃ n : ℕ, ∀ x ∈ s, x ∈ S n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      have haU : a ∈ ⋃ n, S n := hs a (Finset.mem_insert_self a s)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp haU
      have hsRest : ∀ x ∈ s, x ∈ ⋃ n, S n := by
        intro x hx
        exact hs x (Finset.mem_insert_of_mem hx)
      obtain ⟨j, hj⟩ := ih hsRest
      refine ⟨max i j, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxs
      · subst x
        exact hS (Nat.le_max_left i j) hi
      · exact hS (Nat.le_max_right i j) (hj x hxs)

/-- A supported-domain operation preserves increasing unions of
level sets because every vertex has *finite* complete support.
The unrestricted binary-union analogue is false. -/
theorem supportDomain_iUnion_of_monotone
    (support : Vertex → Finset Level)
    (S : ℕ → Set Level) (hS : Monotone S) :
    supportDomain support (⋃ n, S n) =
      ⋃ n, supportDomain support (S n) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hLevels : ∀ q ∈ support x, q ∈ ⋃ n, S n := hx
    obtain ⟨n, hn⟩ :=
      finset_subset_iUnion_of_monotone S hS (support x) hLevels
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact supportDomain_mono support
      (show S n ⊆ ⋃ i, S i from
        fun q hq => Set.mem_iUnion.mpr ⟨n, hq⟩) hn

end BigHrushovski.Ellentuck

namespace BigHrushovski.CFCoherentTower

/-- The actual C_F complete b-support map is jointly locally
determined for every finite set of vertices. -/
theorem birthLevelDomain_local_finset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    ∃ t : Finset ℕ,
      ∀ (S T : Set ℕ),
        (∀ q ∈ t, (q ∈ S ↔ q ∈ T)) →
        ∀ x ∈ s,
          (x ∈ birthLevelDomain F K S ↔
           x ∈ birthLevelDomain F K T) :=
  Ellentuck.supportDomain_local_finset (birthLevelSupport F K) s

/-- Complete-support domains on the genuine countable C_F birth graph
preserve increasing unions of sets of birth levels, *without* a
level-lifting or copy-range theorem. -/
theorem birthLevelDomain_iUnion_of_monotone
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : ℕ → Set ℕ) (hS : Monotone S) :
    birthLevelDomain F K (⋃ n, S n) =
      ⋃ n, birthLevelDomain F K (S n) :=
  Ellentuck.supportDomain_iUnion_of_monotone
    (birthLevelSupport F K) S hS

end BigHrushovski.CFCoherentTower
