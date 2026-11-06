import BigHrushovski.NatStageCoverage
import BigHrushovski.C0UnaryFiniteStrong

/-!
# Coherent finite-valued unary operations on growing initial segments

This abstracts the set-valued unary part of a countable
functional Fraïssé construction. A finite stage on the initial
segment [0,size n) assigns a finite set of vertices to each
current vertex. Old values are preserved *exactly* in every
successor, and each current value lies in the current stage.

Strictly increasing finite sizes cover ℕ. The union operation
C:ℕ→Finset ℕ is therefore defined at the first available
stage, and has exactly the finite value assigned at *any*
later stage. Each finite stage is closed under C, and every
finite set has a finite C-closed stage containing it.

No graph, predimension, functional-extension request or
countable Fraïssé limit is assumed. The lemma can be reused
for other finite-valued unary expansions whenever the same
coherence hypotheses are available.
-/

namespace BigHrushovski

/-- A coherent sequence of finite-valued unary operations on
strictly growing *consecutive* finite intervals. No value
of a vertex in an old stage changes when a new stage is attached. -/
structure CoherentNatUnaryStages where
  size : ℕ → ℕ
  value : ℕ → ℕ → Finset ℕ
  grows : ∀ n : ℕ, size n < size (n + 1)
  supported : ∀ n x : ℕ, x < size n →
    value n x ⊆ Finset.range (size n)
  coherent : ∀ n x : ℕ, x < size n →
    value (n + 1) x = value n x

namespace CoherentNatUnaryStages

variable (S : CoherentNatUnaryStages)

/-- Earlier finite stage domains are included in later ones. -/
theorem size_monotone {n m : ℕ} (hnm : n ≤ m) :
    S.size n ≤ S.size m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact le_refl _
  | succ m ih =>
      by_cases hn : n ≤ m
      · exact (ih hn).trans (Nat.le_of_lt (S.grows m))
      · have hEq : n = m + 1 := by omega
        subst n
        exact le_refl _

/-- Exact preservation of finite unary values across any number
of successor steps. This is equality, not inclusion. -/
theorem value_stable {n m : ℕ} (hnm : n ≤ m)
    {x : ℕ} (hx : x < S.size n) :
    S.value m x = S.value n x := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      by_cases hle : n ≤ m
      · have hxM : x < S.size m :=
          lt_of_lt_of_le hx (S.size_monotone hle)
        calc
          S.value (m + 1) x = S.value m x := S.coherent m x hxM
          _ = S.value n x := ih hle
      · have hn : n = m + 1 := by omega
        subst n
        rfl

/-- Every natural-number vertex eventually belongs to one of the
growing finite stages. -/
theorem vertex_covered (x : ℕ) :
    ∃ n : ℕ, x < S.size n := by
  obtain ⟨n, hn⟩ :=
    FiniteSpan.initialSegment_stages_cover S.size S.grows x
  exact ⟨n, Finset.mem_range.mp hn⟩

/-- One finite stage containing a vertex, chosen only to define
its stable, finite, set-valued unary closure. -/
noncomputable def witnessStage (x : ℕ) : ℕ :=
  Classical.choose (S.vertex_covered x)

theorem witnessStage_contains (x : ℕ) :
    x < S.size (S.witnessStage x) :=
  Classical.choose_spec (S.vertex_covered x)

/-- The value of x in the countable union is its stable value
at one finite stage containing x. -/
noncomputable def limitValue (x : ℕ) : Finset ℕ :=
  S.value (S.witnessStage x) x

/-- The union operation agrees *exactly* with the complete
finite unary value at any selected finite stage. -/
theorem limitValue_eq_stage (n x : ℕ)
    (hx : x < S.size n) :
    S.limitValue x = S.value n x := by
  unfold limitValue
  let m := S.witnessStage x
  have hm : x < S.size m := S.witnessStage_contains x
  rcases le_total n m with hnm | hmn
  · exact S.value_stable hnm hx
  · exact (S.value_stable hmn hm).symm

/-- Every finite stage is closed under the full unary function
of the countable union. No new vertex is admitted into an
old vertex's value after its stage has been constructed. -/
theorem stage_closed (n : ℕ) :
    ∀ x ∈ Finset.range (S.size n),
      S.limitValue x ⊆ Finset.range (S.size n) := by
  intro x hx
  rw [S.limitValue_eq_stage n x (Finset.mem_range.mp hx)]
  exact S.supported n x (Finset.mem_range.mp hx)

/-- Every finite set of vertices is contained in one of the
growing consecutive finite stage domains. -/
theorem finite_stage_cover (s : Finset ℕ) :
    ∃ n : ℕ, s ⊆ Finset.range (S.size n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | @insert x s hx ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm⟩ := S.vertex_covered x
      refine ⟨max n m, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with heq | hyS
      · subst y
        apply Finset.mem_range.mpr
        exact lt_of_lt_of_le hm (S.size_monotone (Nat.le_max_right n m))
      · have hyN : y < S.size n := Finset.mem_range.mp (hn hyS)
        apply Finset.mem_range.mpr
        exact lt_of_lt_of_le hyN (S.size_monotone (Nat.le_max_left n m))

/-- A finite unary-closed cover is supplied automatically by a
stage; no separate unary closure iteration is required. -/
theorem finite_unaryClosed_cover
    (N : GraphOn ℕ) (s : Finset ℕ) :
    ∃ t : Finset ℕ,
      s ⊆ t ∧ N.IsClosedUnderValues S.limitValue t := by
  obtain ⟨n, hn⟩ := S.finite_stage_cover s
  refine ⟨Finset.range (S.size n), hn, ?_⟩
  intro x hx
  exact S.stage_closed n x hx

end CoherentNatUnaryStages
end BigHrushovski
