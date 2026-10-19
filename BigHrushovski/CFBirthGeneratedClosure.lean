import BigHrushovski.CFBirthBlockClosure
import BigHrushovski.Closure

/-!
# Finite generated closures in the actual C_F birth-block structure

The auxiliary unary set-valued operation b of the manuscript forces a
whole fresh tagged block and its actual named old support. The previous
module proved that every finite set closed under this operation is
globally strictly d-closed in the countable birth graph.

We now establish genuine finite generation. A finite set S belongs to
a finite birth stage U_n. The stage image is itself b-closed because
every dependency decreases the birth level. Intersections of b-closed
sets are b-closed, so intersecting all b-closed subsets of U_n which
contain S gives the *least* finite b-closed set containing S.

The leastness is global: if T is any other finite b-closed set in the
countable birth graph, intersect T with U_n first, then use the
finite family of candidate closed subsets inside that stage.
No assumption that T lies inside U_n is made.

This completes the existence assertion of the CF-block-closure-finite
lemma, but not yet the block-root recovery H(R(v))=C(v).
-/

namespace BigHrushovski
namespace CFCoherentTower

variable (F : ℕ → ℝ) (K : ℕ → ℕ)

/-- Birth-level characterization of the actual finite stage image.
It does not depend on how many tagged requests occur at each level. -/
theorem mem_stageImage_iff_birth_lt
    (n : ℕ) (v : Vertex F K) :
    v ∈ stageImage F K n ↔ v.1 < n := by
  classical
  constructor
  · intro hv
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hv
    have h := toVertex_birth_lt F K n u
    rw [hu] at h
    exact h
  · intro h
    obtain ⟨m, fresh⟩ := v
    have hBorn : (⟨m, fresh⟩ : Vertex F K) ∈
        stageImage F K (m + 1) := by
      change (⟨m, fresh⟩ : Vertex F K) ∈
        ((Finset.univ : Finset (stage F K (m+1)).carrier).image
          (toVertex F K (m+1)))
      exact Finset.mem_image.mpr
        ⟨Sum.inr fresh, Finset.mem_univ _, rfl⟩
    exact stageImage_mono F K (Nat.succ_le_of_lt h) hBorn

/-- A whole finite stage is block-support-closed:
each fresh block and its old support occur at earlier levels. -/
theorem stageImage_birthBlockClosed (n : ℕ) :
    IsBirthBlockClosed F K (stageImage F K n) := by
  intro m r i hMem
  have hm : m < n :=
    (mem_stageImage_iff_birth_lt F K n _).mp hMem
  constructor
  · intro j
    exact (mem_stageImage_iff_birth_lt F K n _).mpr hm
  · intro u hu
    have hBirth : (toVertex F K m u).1 < m :=
      toVertex_birth_lt F K m u
    exact (mem_stageImage_iff_birth_lt F K n _).mpr
      (hBirth.trans hm)

/-- Intersections of finite block-closed sets preserve the
complete block values and their old named supports. -/
theorem IsBirthBlockClosed.inter
    {a b : Finset (Vertex F K)}
    (ha : IsBirthBlockClosed F K a)
    (hb : IsBirthBlockClosed F K b) :
    IsBirthBlockClosed F K (a ∩ b) := by
  intro n r i hi
  have hia : (⟨n, (⟨r, i⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ a :=
    (Finset.mem_inter.mp hi).1
  have hib : (⟨n, (⟨r, i⟩ : FreshAt F K n)⟩ : Vertex F K) ∈ b :=
    (Finset.mem_inter.mp hi).2
  obtain ⟨haBlocks, haSupport⟩ := ha n r i hia
  obtain ⟨hbBlocks, hbSupport⟩ := hb n r i hib
  constructor
  · intro j
    exact Finset.mem_inter.mpr ⟨haBlocks j, hbBlocks j⟩
  · intro u hu
    exact Finset.mem_inter.mpr
      ⟨haSupport u hu, hbSupport u hu⟩

/-- Unions of finite block-closed sets are block-closed.
This is the finite-union part of the manuscript lemma. -/
theorem IsBirthBlockClosed.union
    {a b : Finset (Vertex F K)}
    (ha : IsBirthBlockClosed F K a)
    (hb : IsBirthBlockClosed F K b) :
    IsBirthBlockClosed F K (a ∪ b) := by
  intro n r i hi
  rcases Finset.mem_union.mp hi with hiA | hiB
  · obtain ⟨hAll, hSupport⟩ := ha n r i hiA
    exact ⟨fun j => Finset.mem_union.mpr (Or.inl (hAll j)),
      fun u hu => Finset.mem_union.mpr (Or.inl (hSupport u hu))⟩
  · obtain ⟨hAll, hSupport⟩ := hb n r i hiB
    exact ⟨fun j => Finset.mem_union.mpr (Or.inr (hAll j)),
      fun u hu => Finset.mem_union.mpr (Or.inr (hSupport u hu))⟩

/-- The finite intersection of any family of block-closed
sets, taken within a block-closed finite ambient set, remains
block-closed. The empty family gives the ambient set. -/
theorem birthBlockClosed_intersectFamily
    (ambient : Finset (Vertex F K))
    (family : Finset (Finset (Vertex F K)))
    (hAmbient : IsBirthBlockClosed F K ambient)
    (hFamily : ∀ t ∈ family, IsBirthBlockClosed F K t) :
    IsBirthBlockClosed F K
      (Predimension.intersectFamily ambient family) := by
  classical
  induction family using Finset.induction_on with
  | empty =>
      simpa [Predimension.intersectFamily_empty] using hAmbient
  | @insert t others ht ih =>
      have htClosed : IsBirthBlockClosed F K t :=
        hFamily t (Finset.mem_insert_self t others)
      have hRest : ∀ u ∈ others, IsBirthBlockClosed F K u := by
        intro u hu
        exact hFamily u (Finset.mem_insert_of_mem hu)
      rw [Predimension.intersectFamily_insert]
      exact IsBirthBlockClosed.inter F K (ih hRest) htClosed

/-- Every finite set has a least finite b-closed superset in
the original countable tagged carrier. The leastness is with
respect to all finite b-closed supersets, not only supersets
lying in the selected finite stage. -/
theorem exists_least_finite_birthBlockClosure
    (s : Finset (Vertex F K)) :
    ∃ c : Finset (Vertex F K),
      s ⊆ c ∧ IsBirthBlockClosed F K c ∧
      ∀ t : Finset (Vertex F K),
        s ⊆ t → IsBirthBlockClosed F K t → c ⊆ t := by
  classical
  obtain ⟨n, hsStage⟩ := finiteSet_covered F K s
  let ambient := stageImage F K n
  let candidates : Finset (Finset (Vertex F K)) :=
    ambient.powerset.filter
      (fun t => s ⊆ t ∧ IsBirthBlockClosed F K t)
  let c := Predimension.intersectFamily ambient candidates
  have hAmbient : IsBirthBlockClosed F K ambient :=
    stageImage_birthBlockClosed F K n
  have hAll : ∀ t ∈ candidates, IsBirthBlockClosed F K t := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2.2
  have hClosed : IsBirthBlockClosed F K c :=
    birthBlockClosed_intersectFamily F K ambient candidates
      hAmbient hAll
  have hS : s ⊆ c := by
    intro v hv
    change v ∈ Predimension.intersectFamily ambient candidates
    apply Finset.mem_filter.mpr
    refine ⟨hsStage hv, ?_⟩
    intro t ht
    exact (Finset.mem_filter.mp ht).2.1 hv
  refine ⟨c, hS, hClosed, ?_⟩
  intro t hSt htClosed v hv
  have hStageClosed : IsBirthBlockClosed F K (t ∩ ambient) :=
    IsBirthBlockClosed.inter F K htClosed hAmbient
  have hInStage : t ∩ ambient ∈ candidates := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · constructor
      · intro u hu
        exact Finset.mem_inter.mpr ⟨hSt hu, hsStage hu⟩
      · exact hStageClosed
  have hvIn : v ∈ t ∩ ambient :=
    (Finset.mem_filter.mp hv).2 (t ∩ ambient) hInStage
  exact (Finset.mem_inter.mp hvIn).1

end CFCoherentTower
end BigHrushovski
