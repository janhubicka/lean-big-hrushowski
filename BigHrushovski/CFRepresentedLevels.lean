import BigHrushovski.CFSelectedCutEmbedding

/-!
# Represented birth levels of a finite C_F functional source

The finite-level lifting lemma assigns target levels only to the
finitely many source levels that contain actual vertices. At all
other source levels the b-closed stage cut is unchanged, except
for the literal old-stage inclusion.

The assertions here separate these two cases without postulating
a strictly increasing map on ALL source construction levels.
Such a global map may not exist when a finite source vertex born
at level 1 is assigned target level 0.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Literal finite set of birth levels occupied by a finite
subset of the actual countable C_F birth carrier. -/
noncomputable def representedLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Finset ℕ :=
  s.image (fun v => v.1)

/-- A source birth level is represented exactly when its
family of actually selected complete request blocks is nonempty.
No b-closedness is needed for this equivalence. -/
theorem selectedRequests_nonempty_iff_represented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ) :
    (selectedRequests F K s n).Nonempty ↔
      n ∈ representedLevels F K s := by
  classical
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨i, hi⟩ :=
      (mem_selectedRequests_iff F K s n r).mp hr
    exact Finset.mem_image.mpr
      ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi, rfl⟩
  · intro hn
    obtain ⟨v, hv, hvn⟩ := Finset.mem_image.mp hn
    rcases v with ⟨k, fresh⟩
    have hk : k = n := hvn
    subst k
    rcases fresh with ⟨r, i⟩
    exact ⟨r, (mem_selectedRequests_iff F K s n r).mpr ⟨i, hv⟩⟩

/-- At an unrepresented source level, a b-closed finite
source has no fresh block in its successor cut. The next
cut is precisely the literal old-stage image of the
preceding cut, not an artificially renamed copy. -/
theorem stageCut_succ_eq_old_of_unrepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ)
    (hn : n ∉ representedLevels F K s) :
    stageCut F K s (n + 1) =
      (stageCut F K s n).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n+1)).carrier) := by
  classical
  have hEmpty : selectedRequests F K s n = ∅ := by
    ext r
    constructor
    · intro hr
      exact False.elim
        (hn ((selectedRequests_nonempty_iff_represented F K s n).mp
          ⟨r, hr⟩))
    · intro hr
      simp at hr
  simpa [hEmpty] using stageCut_succ_eq_selected F K s hs n

end CFCoherentTower
end BigHrushovski
