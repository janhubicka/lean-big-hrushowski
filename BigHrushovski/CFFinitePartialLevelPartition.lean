import BigHrushovski.FinitePartitionImage
import BigHrushovski.FiniteBlockSupportSubtype
import BigHrushovski.CFBirthBValues
import BigHrushovski.CFBirthTopBlock

/-!
# Exact C_F support and fresh-block images from complete values and birth levels

A finite map on a genuinely partial birth-labelled source need not
be extended to the entire countable graph. If the complete value
of one source birth vertex is transported onto its complete target
value, all source support images have birth level strictly before
the target level, and all source block images have exactly the target
level, both named parts are forced onto the corresponding target
parts. No separate whole-block surjectivity or injectivity is needed.

The hypotheses about birth levels must be proved from the functional
embedding data in the eventual uniqueness argument; graph inducedness
alone is not substituted for these hypotheses.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Under exact complete b-value transport, the old support and
fresh block are separately recovered from the actual target birth
levels. The source map is defined only on the finite subtype s. -/
theorem finitePartial_birthSupport_block_of_levelSplit
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ)
    (r : BirthRequest F K n)
    (t : BirthRequest F K m)
    (i : Fin r.code.1.val)
    (j : Fin t.code.1.val)
    (e : {v : Vertex F K // v ∈ s} → Vertex F K)
    (hValue :
      (selectedFiniteSet s (birthBValue F K
        (⟨n, ⟨r, i⟩⟩ : Vertex F K))).image e =
      birthBValue F K (⟨m, ⟨t, j⟩⟩ : Vertex F K))
    (hOldLevel : ∀ u ∈ selectedFiniteSet s (birthSupport F K n r),
      (e u).1 < m)
    (hNewLevel : ∀ u ∈ selectedFiniteSet s (birthBlock F K n r),
      (e u).1 = m) :
    (selectedFiniteSet s (birthSupport F K n r)).image e =
        birthSupport F K m t ∧
    (selectedFiniteSet s (birthBlock F K n r)).image e =
        birthBlock F K m t := by
  classical
  have hFull :
      ((selectedFiniteSet s (birthSupport F K n r)) ∪
        (selectedFiniteSet s (birthBlock F K n r))).image e =
      birthSupport F K m t ∪ birthBlock F K m t := by
    rw [← selectedFiniteSet_union]
    simpa only [birthBValue_of_fresh] using hValue
  apply union_images_of_separated_parts
    (selectedFiniteSet s (birthSupport F K n r))
    (selectedFiniteSet s (birthBlock F K n r))
    (birthSupport F K m t) (birthBlock F K m t)
    e (fun v : Vertex F K => v.1 = m) hFull
  · intro u hu hEq
    exact (Nat.ne_of_lt (hOldLevel u hu)) hEq
  · intro u hu
    exact hNewLevel u hu
  · intro v hv hEq
    exact (Nat.ne_of_lt (birthSupport_birth_lt F K m t hv)) hEq
  · intro v hv
    exact birthBlock_birth_eq F K m t hv

end CFCoherentTower
end BigHrushovski
