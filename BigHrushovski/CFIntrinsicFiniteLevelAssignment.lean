import BigHrushovski.CFPrescribedFiniteOrderedLift

/-!
# Intrinsic target-level assignments of arbitrary finite C_F maps

The genuine finite existence theorem prescribes target birth levels
only on those source levels containing vertices. For the converse
uniqueness argument, any finite map preserving and reflecting the
birth-level preorder must itself determine a strictly increasing
assignment on exactly those represented source levels.

We choose the target level of any representative of a source level.
Reflection of the birth-level preorder proves independence from
the representative. Values at unused levels are set to zero:
they have no mathematical meaning and need not form an increasing
global self-map of natural numbers.

The resulting assignment is uniquely determined on represented
levels. This requires no graph, b-value or ordering hypotheses,
and therefore can be reused before proving local request-tag
rigidity or any finite uniqueness theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Read the target birth level of an arbitrary finite map at
a represented source level by choosing any vertex on that level.
Unused source levels are set to zero without claiming global
strict monotonicity. -/
noncomputable def finiteEmbeddingLevelMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K) :
    ℕ → ℕ :=
  fun i =>
    if h : ∃ x : SupportCarrier (Vertex F K) s, x.val.1 = i
    then (e (Classical.choose h)).1
    else 0

/-- Reflection of the level preorder makes the target level
independent of which source vertex was chosen at that level.
This includes finite sources whose earliest represented level
is larger than zero and images born at target level zero. -/
theorem finiteEmbeddingLevelMap_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (x : SupportCarrier (Vertex F K) s) :
    (e x).1 = finiteEmbeddingLevelMap F K s e x.val.1 := by
  classical
  unfold finiteEmbeddingLevelMap
  split_ifs with h
  · let y : SupportCarrier (Vertex F K) s := Classical.choose h
    have hy : y.val.1 = x.val.1 := by
      exact (Classical.choose_spec h).trans rfl
    have hxy : BirthLevelLe F K x.val y.val := by
      change x.val.1 ≤ y.val.1
      exact hy.ge
    have hyx : BirthLevelLe F K y.val x.val := by
      change y.val.1 ≤ x.val.1
      exact hy.le
    exact Nat.le_antisymm
      ((heLevel x y).mp hxy)
      ((heLevel y x).mp hyx)
  · exact False.elim (h ⟨x, rfl⟩)

/-- The level assignment extracted from an arbitrary finite map
is strictly increasing on precisely the represented levels,
provided the map reflects and preserves the level preorder. -/
theorem finiteEmbeddingLevelMap_strictOnRepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y)) :
    StrictOnRepresented F K s (finiteEmbeddingLevelMap F K s e) := by
  classical
  intro i hi j hj hij
  obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hi
  obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
  let x : SupportCarrier (Vertex F K) s := ⟨u, hu⟩
  let y : SupportCarrier (Vertex F K) s := ⟨v, hv⟩
  have hBefore : BirthLevelLe F K x.val y.val := by
    change u.1 ≤ v.1
    omega
  have hTarget : (e x).1 < (e y).1 := by
    have hLe : (e x).1 ≤ (e y).1 := (heLevel x y).mp hBefore
    by_contra hNot
    have hBack : BirthLevelLe F K y.val x.val :=
      (heLevel y x).mpr (Nat.le_of_not_gt hNot)
    have hWrong : v.1 ≤ u.1 := hBack
    omega
  have hx : (e x).1 = finiteEmbeddingLevelMap F K s e i := by
    simpa only [x, hui] using
      (finiteEmbeddingLevelMap_exact F K s e heLevel x)
  have hy : (e y).1 = finiteEmbeddingLevelMap F K s e j := by
    simpa only [y, hvj] using
      (finiteEmbeddingLevelMap_exact F K s e heLevel y)
  rw [← hx, ← hy]
  exact hTarget

/-- If some assignment describes the target birth level of
every source vertex, then it necessarily agrees with the
intrinsic assignment on the represented source levels. No
claim about unused levels is possible or required. -/
theorem finiteEmbeddingLevelMap_unique_on_represented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (level : ℕ → ℕ)
    (hExact : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1)
    (i : ℕ) (hi : i ∈ representedLevels F K s) :
    level i = finiteEmbeddingLevelMap F K s e i := by
  classical
  obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
  let x : SupportCarrier (Vertex F K) s := ⟨v, hv⟩
  have hEq : level x.val.1 = finiteEmbeddingLevelMap F K s e x.val.1 :=
    (hExact x).symm.trans
      (finiteEmbeddingLevelMap_exact F K s e heLevel x)
  simpa only [x, hvi] using hEq

/-- Every finite birth-level-preorder embedding supplies its own
strictly increasing represented-level assignment. Its values
are forced by the embedding on all source vertices, without
requiring a global increasing self-map of natural numbers. -/
theorem finiteEmbedding_has_strict_level_assignment
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y)) :
    ∃ level : ℕ → ℕ,
      StrictOnRepresented F K s level ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (e x).1 = level x.val.1) := by
  refine ⟨finiteEmbeddingLevelMap F K s e, ?_, ?_⟩
  · exact finiteEmbeddingLevelMap_strictOnRepresented F K s e heLevel
  · exact finiteEmbeddingLevelMap_exact F K s e heLevel

end CFCoherentTower
end BigHrushovski
