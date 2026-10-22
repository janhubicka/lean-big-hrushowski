import BigHrushovski.CFBirthGeneratedTransport
import BigHrushovski.CFRHToBValues

/-!
# First vertices and the admissible order inside C_F birth blocks

A literal fresh block is indexed by Fin n in its chosen order.
The distinguished first vertex is therefore exactly the vertex
with ordinal zero. We expose this fact without imposing an
unrelated total order on the entire countable birth carrier.

If a map takes every complete birth block onto the corresponding
target block and is increasing on each finite block, then it
carries first vertices to first vertices. Complete b-value
preservation plus reflection of the birth-level preorder
supplies the required exact image of blocks. Injectivity
then reflects first-vertex status, which is the domain
predicate for the partial function H.

Combined with the earlier complete-value transport lemmas,
this proves b- and (R,H)-value equivalence for globally
induced self-maps with the specified order and level
hypotheses. A final source-substructure formulation, with
maps defined only on an arbitrary closed subset, is distinct.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The finite ordinal assigned to a fresh vertex inside its
literal tagged request block. -/
def birthOrdinal (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Vertex F K → ℕ
  | ⟨_, ⟨_, i⟩⟩ => i.val

/-- Exact birth-level preorder. Its symmetric part is equality
of birth levels, the only fact needed to recognize top blocks. -/
def BirthLevelLe (F : ℕ → ℝ) (K : ℕ → ℕ)
    (u v : Vertex F K) : Prop :=
  u.1 ≤ v.1

/-- Reflection and preservation of the level preorder implies
reflection and preservation of equality of birth levels. -/
theorem birthLevelEq_of_preorder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hLevel : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (u v : Vertex F K) :
    u.1 = v.1 ↔ (f u).1 = (f v).1 := by
  constructor
  · intro huv
    exact Nat.le_antisymm
      ((hLevel u v).mp (Nat.le_of_eq huv))
      ((hLevel v u).mp (Nat.le_of_eq huv.symm))
  · intro huv
    exact Nat.le_antisymm
      ((hLevel u v).mpr (Nat.le_of_eq huv))
      ((hLevel v u).mpr (Nat.le_of_eq huv.symm))

/-- The distinguished first vertex belongs to its literal whole
fresh block, also when v is a later ordinal of that block. -/
theorem rootOf_mem_birthBlockOf
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K) :
    rootOf F K v ∈ birthBlockOf F K v := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  exact birthRoot_mem_block F K n r

/-- The first vertex has ordinal zero by the finite block code. -/
theorem birthOrdinal_rootOf
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K) :
    birthOrdinal F K (rootOf F K v) = 0 := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  rfl

/-- In a fixed literal birth block the only vertex of ordinal
zero is its designated first vertex. -/
theorem birthOrdinal_zero_eq_root_of_mem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v w : Vertex F K)
    (hw : w ∈ birthBlockOf F K v)
    (hZero : birthOrdinal F K w = 0) :
    w = rootOf F K v := by
  classical
  rcases v with ⟨n, ⟨r, i⟩⟩
  change w ∈ birthBlock F K n r at hw
  obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hw
  obtain ⟨j, _, hjz⟩ := Finset.mem_image.mp hz
  have hwj : w = (⟨n, ⟨r, j⟩⟩ : Vertex F K) := by
    calc
      w = toVertex F K (n + 1) z := hzw.symm
      _ = toVertex F K (n + 1) (Sum.inr ⟨r, j⟩) := by rw [hjz]
      _ = (⟨n, ⟨r, j⟩⟩ : Vertex F K) := rfl
  rw [hwj] at hZero ⊢
  have hj : j.val = 0 := hZero
  have hj0 : j = ⟨0, r.code.2.fresh_pos⟩ :=
    Fin.ext hj
  rw [hj0]
  rfl

/-- A map is increasing in each finite ordered birth block.
This is exactly the part of the admissible order needed to
select the first vertex, without choosing an arbitrary order
between different request tags. -/
def PreservesBirthBlockOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) : Prop :=
  ∀ v u w : Vertex F K,
    u ∈ birthBlockOf F K v →
    w ∈ birthBlockOf F K v →
    birthOrdinal F K u < birthOrdinal F K w →
    birthOrdinal F K (f u) < birthOrdinal F K (f w)

/-- Exact images of complete blocks and their internal strict
order determine the image of every distinguished first vertex.
No global order on unrelated blocks is required. -/
theorem rootOf_image_of_blockOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hBlocks : ∀ v : Vertex F K,
      (birthBlockOf F K v).image f = birthBlockOf F K (f v))
    (hOrder : PreservesBirthBlockOrder F K f)
    (v : Vertex F K) :
    f (rootOf F K v) = rootOf F K (f v) := by
  classical
  have hRootIn : rootOf F K v ∈ birthBlockOf F K v :=
    rootOf_mem_birthBlockOf F K v
  have hTargetRoot :
      rootOf F K (f v) ∈ (birthBlockOf F K v).image f := by
    rw [hBlocks v]
    exact rootOf_mem_birthBlockOf F K (f v)
  obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hTargetRoot
  by_cases hZero : birthOrdinal F K w = 0
  · have hEq : w = rootOf F K v :=
      birthOrdinal_zero_eq_root_of_mem F K v w hw hZero
    rw [hEq] at hfw
    exact hfw
  · have hPositive : 0 < birthOrdinal F K w :=
      Nat.pos_of_ne_zero hZero
    have hStrict :
        birthOrdinal F K (f (rootOf F K v)) <
          birthOrdinal F K (f w) :=
      hOrder v (rootOf F K v) w hRootIn hw (by
        rw [birthOrdinal_rootOf F K v]
        exact hPositive)
    rw [hfw, birthOrdinal_rootOf F K (f v)] at hStrict
    exact False.elim ((Nat.not_lt_zero _) hStrict)

/-- The complete b-values, level preorder and internal block
order together force the correct first vertices of all blocks. -/
theorem rootOf_image_of_bValues_order
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrder F K f)
    (v : Vertex F K) :
    f (rootOf F K v) = rootOf F K (f v) := by
  have hC : ∀ u : Vertex F K,
      (birthCValue F K u).image f = birthCValue F K (f u) := by
    intro u
    have hImage :=
      birthGeneratedClosure_image_of_bValues F K f
        ({u} : Finset (Vertex F K)) (fun x _ => hB x)
    simpa only [birthCValue, Finset.image_singleton] using hImage
  have hBlocks : ∀ u : Vertex F K,
      (birthBlockOf F K u).image f = birthBlockOf F K (f u) :=
    fun u =>
      birthBlockOf_image_of_closure_levels F K f hC
        (fun x y => birthLevelEq_of_preorder F K f hLevel x y) u
  exact rootOf_image_of_blockOrder F K f hBlocks hOrder v

/-- Under complete b-values and internal block order, an
injective embedding preserves *and reflects* the partial
domain of H: finite sets consisting only of actual block roots. -/
theorem rootDomain_iff_image_of_bValues_order
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrder F K f)
    (s : Finset (Vertex F K)) :
    (∀ r ∈ s, IsBirthRoot F K r) ↔
      (∀ r ∈ s.image f, IsBirthRoot F K r) := by
  have hRoot : ∀ v : Vertex F K,
      f (rootOf F K v) = rootOf F K (f v) :=
    rootOf_image_of_bValues_order F K f hB hLevel hOrder
  constructor
  · intro hs r hr
    obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp hr
    rw [← hvr]
    exact (isBirthRoot_iff_image F K f hf hRoot v).mp (hs v hv)
  · intro hs v hv
    apply (isBirthRoot_iff_image F K f hf hRoot v).mpr
    exact hs (f v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Complete value equivalence for globally induced C_F birth
self-maps preserving and reflecting the level preorder and
preserving the natural order inside each fresh block.

These two value predicates are equivalent under the same map:
(1) f carries each entire auxiliary b(v) exactly onto b(fv);
(2) f carries every R(v) and every defined H(S) exactly onto
    their corresponding target values.

The domain reflection of H follows separately from the
first-root theorem above. Arbitrary closed-source embeddings
need a subtype/restriction formulation; this is not assumed. -/
theorem bValues_iff_RHValues_of_birthOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hLevel : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrder F K f) :
    (∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v : Vertex F K,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) := by
  constructor
  · intro hB
    have hRoot : ∀ v : Vertex F K,
        f (rootOf F K v) = rootOf F K (f v) :=
      rootOf_image_of_bValues_order F K f hB hLevel hOrder
    constructor
    · exact birthReachableRoots_image_of_bValues F K f hB hRoot
    · intro s _
      exact birthDClosedHull_image_of_all_bValues F K f hf hAdj hB s
  · rintro ⟨hR, hH⟩
    intro v
    exact birthBValue_image_of_RHValues F K f hf hAdj
      (fun x y => birthLevelEq_of_preorder F K f hLevel x y)
      hR hH v

end CFCoherentTower
end BigHrushovski
