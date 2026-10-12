import BigHrushovski.C0MinimalTraces

/-!
# Prefix offsets for concatenating finite minimal-step segments

Let \`length n > 0\` be the length of each finite source-stage list.
The partial sums \`offset length n\` delimit consecutive blocks.
Every natural number belongs to a unique half-open block
\`[offset n, offset (n+1))\`; its block number is the least \`n\`
for which the upper bound exceeds the index.

This arithmetic is independent of the Hrushovski graph. Its
specific instance is the nonempty trace lists of the strong
C0 skeleton. No dummy boundary stages are inserted.
-/

namespace BigHrushovski
namespace Predimension
namespace C0Offsets

/-- Number of stages already supplied by the first \`n\` blocks. -/
def offset (length : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => offset length n + length n

theorem offset_succ (length : ℕ → ℕ) (n : ℕ) :
    offset length (n + 1) = offset length n + length n := rfl

theorem offset_mono (length : ℕ → ℕ) :
    Monotone (offset length) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ m _ ih =>
      calc
        offset length n ≤ offset length m := ih
        _ ≤ offset length (m + 1) := by
          rw [offset_succ]
          omega

/-- If each finite block is nonempty, its cumulative length is
at least the number of blocks. -/
theorem index_le_offset (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (n : ℕ) :
    n ≤ offset length n := by
  induction n with
  | zero => simp [offset]
  | succ n ih =>
      rw [offset_succ]
      have hp := hpos n
      omega

theorem exists_cover (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (i : ℕ) :
    ∃ n : ℕ, i < offset length (n + 1) := by
  refine ⟨i, ?_⟩
  have h := index_le_offset length hpos (i + 1)
  omega

/-- The unique finite segment that contributes the i-th stage. -/
noncomputable def block (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (i : ℕ) : ℕ :=
  Nat.find (exists_cover length hpos i)

theorem block_upper (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (i : ℕ) :
    i < offset length (block length hpos i + 1) :=
  Nat.find_spec (exists_cover length hpos i)

/-- The chosen block cannot start after the requested index:
otherwise the preceding block would already have covered it. -/
theorem block_lower (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (i : ℕ) :
    offset length (block length hpos i) ≤ i := by
  by_cases hzero : block length hpos i = 0
  · simp [hzero, offset]
  · have hpred : block length hpos i - 1 <
        block length hpos i := by omega
    have hmin : ¬ i <
        offset length (block length hpos i - 1 + 1) := by
      exact Nat.find_min (exists_cover length hpos i)
        (by simpa only [block] using hpred)
    have heq : block length hpos i - 1 + 1 =
        block length hpos i := by omega
    rw [heq] at hmin
    omega

theorem local_index_lt (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n) (i : ℕ) :
    i - offset length (block length hpos i) <
      length (block length hpos i) := by
  have hlo := block_lower length hpos i
  have hhi := block_upper length hpos i
  rw [offset_succ] at hhi
  omega

/-- A half-open offset interval determines its block uniquely. -/
theorem block_eq_of_interval (length : ℕ → ℕ)
    (hpos : ∀ n, 0 < length n)
    (i n : ℕ)
    (hlo : offset length n ≤ i)
    (hhi : i < offset length (n + 1)) :
    block length hpos i = n := by
  have hu := block_upper length hpos i
  have hl := block_lower length hpos i
  by_contra hne
  by_cases hlt : block length hpos i < n
  · have hmono := offset_mono length
      (show block length hpos i + 1 ≤ n by omega)
    omega
  · have hmono := offset_mono length
      (show n + 1 ≤ block length hpos i by omega)
    omega

end C0Offsets
end Predimension

namespace FiniteCatalogue

/-- Each list of starting stages from the certified minimal
refinement contributes its number of genuine minimal steps. -/
noncomputable def genericC0SegmentLength (n : ℕ) : ℕ :=
  (genericC0SegmentTrace n).starts.length

theorem genericC0SegmentLength_pos (n : ℕ) :
    0 < genericC0SegmentLength n :=
  genericC0SegmentTrace_nonempty n

/-- The index of the finite minimal-refinement segment that
contains the given position in the eventual omega enumeration. -/
noncomputable def genericC0BlockIndex (i : ℕ) : ℕ :=
  Predimension.C0Offsets.block genericC0SegmentLength
    genericC0SegmentLength_pos i

theorem genericC0BlockIndex_bounds (i : ℕ) :
    Predimension.C0Offsets.offset genericC0SegmentLength
       (genericC0BlockIndex i) ≤ i ∧
    i < Predimension.C0Offsets.offset genericC0SegmentLength
       (genericC0BlockIndex i + 1) :=
  ⟨Predimension.C0Offsets.block_lower _ genericC0SegmentLength_pos i,
   Predimension.C0Offsets.block_upper _ genericC0SegmentLength_pos i⟩

theorem genericC0LocalIndex_lt (i : ℕ) :
    i - Predimension.C0Offsets.offset genericC0SegmentLength
      (genericC0BlockIndex i) <
        genericC0SegmentLength (genericC0BlockIndex i) :=
  Predimension.C0Offsets.local_index_lt _ genericC0SegmentLength_pos i

end FiniteCatalogue
end BigHrushovski
