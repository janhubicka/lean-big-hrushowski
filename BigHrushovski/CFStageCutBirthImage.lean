import BigHrushovski.CFRepresentedLevels
import BigHrushovski.CFBirthGeneratedClosure

/-!
# Literal birth-labelled images of C_F stage cuts

A finite source has a concrete subset of the canonical birth-labelled
C_F carrier. Its cut in stage n is defined by testing membership in
that subset. Under the canonical stage-to-birth injection this cut
is EXACTLY the vertices of the source born before n.

Thus source stages can be compared across arbitrarily long gaps
using literal birth-label sets instead of repeated inverses
between different dependent finite stage carrier types. If no
source birth level lies in [n,m), the two images are equal.

No b-closure assumption or prescribed target-map assumption
is needed for these elementary source-cut facts.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The literal birth-labelled image of the finite source stage cut
contains exactly the source vertices born before that stage. -/
theorem stageCut_birthImage_eq_filter
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ) :
    (stageCut F K s n).image (toVertex F K n) =
      s.filter (fun v => v.1 < n) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← huv]
      exact (mem_stageCut_iff F K s n u).mp hu
    · rw [← huv]
      exact toVertex_birth_lt F K n u
  · intro hv
    obtain ⟨hvs, hvn⟩ := Finset.mem_filter.mp hv
    have hStage : v ∈ stageImage F K n :=
      (mem_stageImage_iff_birth_lt F K n v).mpr hvn
    obtain ⟨u, _, huv⟩ := Finset.mem_image.mp hStage
    apply Finset.mem_image.mpr
    refine ⟨u, ?_, huv⟩
    apply (mem_stageCut_iff F K s n u).mpr
    rw [huv]
    exact hvs

/-- If the source vertices have the same birth-level comparison
with n and m, their literal stage-cut birth images are equal.
No chosen stage embedding or graph isomorphism appears. -/
theorem stageCut_birthImage_eq_of_comparison
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (h : ∀ v ∈ s, v.1 < n ↔ v.1 < m) :
    (stageCut F K s n).image (toVertex F K n) =
      (stageCut F K s m).image (toVertex F K m) := by
  rw [stageCut_birthImage_eq_filter, stageCut_birthImage_eq_filter]
  ext v
  constructor
  · intro hv
    obtain ⟨hvs, hlt⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hvs, (h v hvs).mp hlt⟩
  · intro hv
    obtain ⟨hvs, hlt⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hvs, (h v hvs).mpr hlt⟩

/-- If a finite source has no represented birth level in the
half-open interval [n,m), its actual two stage cuts have the
same literal set of birth-labelled vertices. In particular this
covers arbitrary gaps between successive represented levels. -/
theorem stageCut_birthImage_eq_of_noLevelsBetween
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i) :
    (stageCut F K s n).image (toVertex F K n) =
      (stageCut F K s m).image (toVertex F K m) := by
  apply stageCut_birthImage_eq_of_comparison F K s n m
  intro v hv
  constructor
  · intro hlt
    exact lt_of_lt_of_le hlt hnm
  · intro hlt
    have hvLevel : v.1 ∈ representedLevels F K s :=
      Finset.mem_image.mpr ⟨v, hv, rfl⟩
    rcases hGap v.1 hvLevel with hbefore | hafter
    · exact hbefore
    · exact False.elim ((not_lt_of_ge hafter) hlt)

end CFCoherentTower
end BigHrushovski
