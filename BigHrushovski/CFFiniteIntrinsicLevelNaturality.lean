import BigHrushovski.CFIntrinsicFiniteLevelAssignment
import BigHrushovski.CFFiniteClosedSourceRestriction
import BigHrushovski.CFFiniteClosedImageNaturality

/-!
# Restriction and composition of finite intrinsic C_F level maps

An arbitrary finite map reflecting the birth-level preorder
determines an increasing assignment on its finitely represented
source levels. This note shows that the assignment is compatible
with literal restriction to a smaller finite source, and with
composition through the literal finite image.

These statements do not use graph adjacency, any unary b-value,
or the R,H operations. In particular they introduce no spurious
closedness or global monotonicity assumption. They apply equally
to the finite graphs and the ordered functional expansion.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The level map extracted from a finite preorder embedding
commutes with restriction on represented source levels.

The source s need only be a subset of t; neither is required
to be closed, because this is purely a statement about
preservation and reflection of the level preorder. -/
theorem finiteEmbeddingLevelMap_restriction_on_represented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hst : s ⊆ t)
    (e : SupportCarrier (Vertex F K) t → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) t,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (i : ℕ) (hi : i ∈ representedLevels F K s) :
    finiteEmbeddingLevelMap F K s
      (fun x => e (finiteClosedSourceInclusion F K s t hst x)) i =
    finiteEmbeddingLevelMap F K t e i := by
  let inc := finiteClosedSourceInclusion F K s t hst
  let r : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => e (inc x)
  have hrLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (r x) (r y) := by
    intro x y
    exact heLevel (inc x) (inc y)
  have hrBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (r x).1 = finiteEmbeddingLevelMap F K t e x.val.1 := by
    intro x
    exact finiteEmbeddingLevelMap_exact
      F K t e heLevel (inc x)
  exact (finiteEmbeddingLevelMap_unique_on_represented
    F K s r hrLevel
    (finiteEmbeddingLevelMap F K t e) hrBirth i hi).symm

/-- On represented source levels, the intrinsic target-level
map of a genuine partial composite is the composition of the
two intrinsic target-level maps.

The second map is defined on the *literal finite image*
of the first, not on a selected full finite stage. The
conclusion concerns represented levels only: the arbitrary
default values assigned at absent levels are immaterial. -/
theorem finiteEmbeddingLevelMap_composition_on_represented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (g : SupportCarrier (Vertex F K)
      (finiteBirthSourceImage F K s e) → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (hgLevel : ∀ x y : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (g x) (g y))
    (i : ℕ) (hi : i ∈ representedLevels F K s) :
    finiteEmbeddingLevelMap F K s
      (fun x => g (finiteBirthSourceImagePoint F K s e x)) i =
    finiteEmbeddingLevelMap F K
      (finiteBirthSourceImage F K s e) g
        (finiteEmbeddingLevelMap F K s e i) := by
  let t := finiteBirthSourceImage F K s e
  let j := finiteBirthSourceImagePoint F K s e
  let c : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => g (j x)
  have hcLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (c x) (c y) := by
    intro x y
    exact (heLevel x y).trans (hgLevel (j x) (j y))
  have hcBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (c x).1 =
        finiteEmbeddingLevelMap F K t g
          (finiteEmbeddingLevelMap F K s e x.val.1) := by
    intro x
    calc
      (c x).1 =
          finiteEmbeddingLevelMap F K t g (j x).val.1 :=
        finiteEmbeddingLevelMap_exact F K t g hgLevel (j x)
      _ = finiteEmbeddingLevelMap F K t g
          (finiteEmbeddingLevelMap F K s e x.val.1) := by
        change finiteEmbeddingLevelMap F K t g (e x).1 =
          finiteEmbeddingLevelMap F K t g
            (finiteEmbeddingLevelMap F K s e x.val.1)
        rw [finiteEmbeddingLevelMap_exact F K s e heLevel x]
  exact (finiteEmbeddingLevelMap_unique_on_represented
    F K s c hcLevel
    (fun k => finiteEmbeddingLevelMap F K t g
      (finiteEmbeddingLevelMap F K s e k))
    hcBirth i hi).symm

/-- The composite of two intrinsic finite level maps is
strictly increasing on the levels represented in the original
source. There is deliberately no claim about the values
assigned to unrepresented levels. -/
theorem finiteEmbeddingLevelMap_comp_strictOnRepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (g : SupportCarrier (Vertex F K)
      (finiteBirthSourceImage F K s e) → Vertex F K)
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (hgLevel : ∀ x y : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (g x) (g y)) :
    StrictOnRepresented F K s
      (fun i =>
        finiteEmbeddingLevelMap F K
          (finiteBirthSourceImage F K s e) g
          (finiteEmbeddingLevelMap F K s e i)) := by
  let j := finiteBirthSourceImagePoint F K s e
  let c : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => g (j x)
  have hcLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (c x) (c y) := by
    intro x y
    exact (heLevel x y).trans (hgLevel (j x) (j y))
  intro i hi k hk hik
  have hStrict := finiteEmbeddingLevelMap_strictOnRepresented
    F K s c hcLevel i hi k hk hik
  calc
    finiteEmbeddingLevelMap F K
      (finiteBirthSourceImage F K s e) g
        (finiteEmbeddingLevelMap F K s e i) =
      finiteEmbeddingLevelMap F K s c i :=
        (finiteEmbeddingLevelMap_composition_on_represented
          F K s e g heLevel hgLevel i hi).symm
    _ < finiteEmbeddingLevelMap F K s c k := hStrict
    _ = finiteEmbeddingLevelMap F K
        (finiteBirthSourceImage F K s e) g
          (finiteEmbeddingLevelMap F K s e k) :=
        finiteEmbeddingLevelMap_composition_on_represented
          F K s e g heLevel hgLevel k hk

end CFCoherentTower
end BigHrushovski
