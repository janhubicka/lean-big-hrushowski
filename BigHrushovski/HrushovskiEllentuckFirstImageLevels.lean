import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness

/-!
# Exact finite approximations by first represented image levels

Let f be a global map of the actual C_F birth carrier with
birth-level action h. If h is strictly increasing, the image
of the literal finite stage U_n is precisely the part of
range(f) on the level set h[{0,...,n-1}]. The proof uses
only stage coverage and the level equation.

If every birth level contains an empty-support request,
all of these image levels occur, so they are exactly the
first n represented levels of the copy. The second
hypothesis cannot be omitted in a presentation with
empty birth layers.

No abstract Ramsey-space axiom or identification of
the natural topology is used here.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- The image of the first n complete birth stages is exactly
the part of a global embedding range on the first n image
levels. This holds even before finite uniqueness or the
embedding's functional-value equations are considered. -/
theorem stageImage_under_level_map
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1)
    (n : ℕ) :
    Set.image f (↑(stageImage F K n) : Set (Vertex F K)) =
      {w : Vertex F K |
        w ∈ Set.range f ∧
        w.1 ∈ Set.image h (Set.Iio n)} := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, rfl⟩, ⟨v.1, ?_, ?_⟩⟩
    · exact (mem_stageImage_iff_birth_lt F K n v).mp hv
    · exact (hBirth v).symm
  · rintro ⟨⟨v, rfl⟩, ⟨k, hk, hkv⟩⟩
    have hEq : h k = h v.1 := hkv.trans (hBirth v)
    have hkEq : k = v.1 := hh.injective hEq
    refine ⟨v, ?_, rfl⟩
    apply (mem_stageImage_iff_birth_lt F K n v).mpr
    simpa only [hkEq] using hk

/-- The birth levels represented in a set of vertices. -/
def representedBirthLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K)) : Set ℕ :=
  {q | ∃ w ∈ X, w.1 = q}

/-- A finite stage image realizes every level in h[{0,...,n-1}]
when an actual vertex is born at each original source level.
This identifies the finite approximation as the first n
*represented* image levels, rather than merely a subset
of the allowed image levels. -/
theorem representedBirthLevels_stageImage_under_level_map
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ k : ℕ, ∃ r : BirthRequest F K k,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (h : ℕ → ℕ)
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1)
    (n : ℕ) :
    representedBirthLevels F K
        (Set.image f (↑(stageImage F K n) : Set (Vertex F K))) =
      Set.image h (Set.Iio n) := by
  ext q
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, hq⟩
    exact ⟨v.1, (mem_stageImage_iff_birth_lt F K n v).mp hv,
      (hBirth v).symm.trans hq⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨r, hr⟩ := hReq k
    let v : Vertex F K := birthRoot F K k r
    have hv : v ∈ stageImage F K n := by
      apply (mem_stageImage_iff_birth_lt F K n v).mpr
      change k < n
      exact hk
    refine ⟨f v, ⟨v, hv, rfl⟩, ?_⟩
    change (f v).1 = h k
    exact hBirth v

/-- Under the same level-witness condition the birth-level set
represented in an entire global image equals range(h).
The singleton-support request supplies the required vertex
on every source level. -/
theorem representedBirthLevels_range_under_level_map
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ k : ℕ, ∃ r : BirthRequest F K k,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (h : ℕ → ℕ)
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1) :
    representedBirthLevels F K (Set.range f) = Set.range h := by
  ext q
  constructor
  · rintro ⟨w, ⟨v, rfl⟩, hq⟩
    exact ⟨v.1, (hBirth v).symm.trans hq⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨r, hr⟩ := hReq k
    let v : Vertex F K := birthRoot F K k r
    refine ⟨f v, ⟨v, rfl⟩, ?_⟩
    change (f v).1 = h k
    exact hBirth v

end BigHrushovski.CFCoherentTower
