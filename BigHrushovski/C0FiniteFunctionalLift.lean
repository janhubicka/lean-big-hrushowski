import BigHrushovski.C0FiniteAppend
import BigHrushovski.C0MinimalBlockRuns

/-!
# Lift any finite strong graph extension to a canonical C0 unary expansion

Given a finite induced old graph a carrying a canonical minimal-block
index κ and a finite strong extension a ≤ V, first extract the literal
list of disjoint minimal strong blocks from the graph extension.
Assign the old vertices their original indices, and assign every new
vertex the first position in that block list where it appears.

We prove that the resulting single component-index map is a canonical
minimal-strong presentation of V and its complete set-valued unary
function restricts exactly to the original unary function on a.

This closes the finite graph-to-functional lifting step for a literal
strong inclusion. No global strong exhaustion or countable Fraïssé
construction is required.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- The initial union of a finite list of fresh components. -/
def blockPrefix : List (Finset V) → ℕ → Finset V
  | _, 0 => ∅
  | [], _ + 1 => ∅
  | B :: rest, i + 1 => B ∪ blockPrefix rest i

/-- Chronological position of the first component containing v.
Vertices outside every block receive the sentinel index
blocks.length. -/
def blockIndex : List (Finset V) → V → ℕ
  | [], _ => 0
  | B :: rest, v =>
      if v ∈ B then 0 else blockIndex rest v + 1

/-- Every position below the length of the block list corresponds
exactly to membership in the union of the earlier blocks. -/
theorem mem_blockPrefix_iff (blocks : List (Finset V))
    (v : V) :
    ∀ i : ℕ, i ≤ blocks.length →
      (v ∈ blockPrefix blocks i ↔ blockIndex blocks v < i) := by
  induction blocks with
  | nil =>
      intro i hi
      have hzero : i = 0 := by simpa only [List.length_nil] using hi
      subst i
      simp [blockPrefix, blockIndex]
  | cons B rest ih =>
      intro i hi
      cases i with
      | zero =>
          simp [blockPrefix]
      | succ j =>
          have hj : j ≤ rest.length := by
            simp only [List.length_cons] at hi
            omega
          have hRest := ih j hj
          by_cases hv : v ∈ B
          · simp [blockPrefix, blockIndex, hv]
          · simp only [blockPrefix, Finset.mem_union]
            simp only [blockIndex, if_neg hv, Nat.add_lt_add_iff_right]
            simpa [hv] using hRest

/-- The fold of disjoint fresh blocks is the old set together
with the union of all blocks in the list. -/
theorem blockRunEnd_eq_prefix
    (a : Finset V) (blocks : List (Finset V)) :
    Predimension.blockRunEnd a blocks =
      a ∪ blockPrefix blocks blocks.length := by
  induction blocks generalizing a with
  | nil =>
      simp [Predimension.blockRunEnd, blockPrefix]
  | cons B rest ih =>
      calc
        Predimension.blockRunEnd a (B :: rest) =
            Predimension.blockRunEnd (a ∪ B) rest := rfl
        _ = (a ∪ B) ∪ blockPrefix rest rest.length := ih (a ∪ B)
        _ = a ∪ blockPrefix (B :: rest) (B :: rest).length := by
          simp only [List.length_cons, blockPrefix]
          ac_rfl

/-- Every vertex outside the old set belongs to one of the
new blocks, so its first-block index is strictly below the
length of the list. -/
theorem blockIndex_lt_of_cover
    (a : Finset V) (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (v : V) (hv : v ∉ a) :
    blockIndex blocks v < blocks.length := by
  have hvEnd : v ∈ Predimension.blockRunEnd a blocks := by
    rw [hCover]
    exact Finset.mem_univ _
  rw [blockRunEnd_eq_prefix a blocks] at hvEnd
  rcases Finset.mem_union.mp hvEnd with hOld | hNew
  · exact (hv hOld).elim
  · exact (mem_blockPrefix_iff blocks v blocks.length
      (le_refl _)).mp hNew

/-- The complete canonical indexing of an arbitrary finite strong
extension: old vertices keep their old component numbers and
the fresh vertices are numbered in the order of the block list. -/
noncomputable def extendRunIndex
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (v : V) : Fin (n + blocks.length) :=
  if h : v ∈ a then
    ⟨(κ ⟨v, h⟩).val, by omega⟩
  else
    ⟨n + blockIndex blocks v,
      by
        have hIndex := blockIndex_lt_of_cover a blocks hCover v h
        omega⟩

theorem extendRunIndex_old
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (v : {v : V // v ∈ a}) :
    (extendRunIndex a κ blocks hCover v.val).val = (κ v).val := by
  simp [extendRunIndex, v.property]

theorem extendRunIndex_fresh
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (v : V) (hv : v ∉ a) :
    (extendRunIndex a κ blocks hCover v).val =
      n + blockIndex blocks v := by
  simp [extendRunIndex, hv]

/-- Every old indexed stage has precisely the same vertex image
in the enlarged graph. -/
theorem oldStage_extend_image
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (k : ℕ) (hk : k ≤ n) :
    oldStage (extendRunIndex a κ blocks hCover) k =
      (oldStage κ k).image (Subtype.val : {v : V // v ∈ a} → V) := by
  classical
  ext v
  constructor
  · intro hv
    have hlt : (extendRunIndex a κ blocks hCover v).val < k :=
      (mem_oldStage_iff (extendRunIndex a κ blocks hCover) k v).mp hv
    by_cases ha : v ∈ a
    · exact Finset.mem_image.mpr
        ⟨⟨v, ha⟩,
          (mem_oldStage_iff κ k ⟨v, ha⟩).mpr (by
            rw [extendRunIndex_old a κ blocks hCover ⟨v, ha⟩] at hlt
            exact hlt), rfl⟩
    · rw [extendRunIndex_fresh a κ blocks hCover v ha] at hlt
      omega
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    have hlt : (κ u).val < k := (mem_oldStage_iff κ k u).mp hu
    rw [← huv]
    exact (mem_oldStage_iff (extendRunIndex a κ blocks hCover)
      k u.val).mpr (by
        rw [extendRunIndex_old a κ blocks hCover u]
        exact hlt)

/-- The old graph is exactly stage n of the enlarged indexing. -/
theorem oldStage_extend_old
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ) :
    oldStage (extendRunIndex a κ blocks hCover) n = a := by
  classical
  rw [oldStage_extend_image a κ blocks hCover n (le_refl n),
    oldStage_final κ]
  ext v
  constructor
  · intro hv
    obtain ⟨u, _, hEq⟩ := Finset.mem_image.mp hv
    rw [← hEq]
    exact u.property
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

/-- After the old prefix, the j-th stage is exactly the old graph
together with the first j new fresh blocks. -/
theorem oldStage_extend_later
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (j : ℕ) (hj : j ≤ blocks.length) :
    oldStage (extendRunIndex a κ blocks hCover) (n+j) =
      a ∪ blockPrefix blocks j := by
  classical
  ext v
  by_cases hvOld : v ∈ a
  · have hvIndex : (extendRunIndex a κ blocks hCover v).val < n+j := by
      rw [extendRunIndex_old a κ blocks hCover ⟨v,hvOld⟩]
      have hlt : (κ ⟨v,hvOld⟩).val < n := (κ ⟨v,hvOld⟩).isLt
      omega
    constructor
    · intro _
      exact Finset.mem_union.mpr (Or.inl hvOld)
    · intro _
      exact (mem_oldStage_iff (extendRunIndex a κ blocks hCover) (n+j) v).mpr hvIndex
  · have hvVal := extendRunIndex_fresh a κ blocks hCover v hvOld
    have hPrefix := mem_blockPrefix_iff blocks v j hj
    constructor
    · intro hv
      have hlt : (extendRunIndex a κ blocks hCover v).val < n+j :=
        (mem_oldStage_iff (extendRunIndex a κ blocks hCover) (n+j) v).mp hv
      have hIdx : blockIndex blocks v < j := by omega
      exact Finset.mem_union.mpr (Or.inr (hPrefix.mpr hIdx))
    · intro hv
      rcases Finset.mem_union.mp hv with ha | hPrefixV
      · exact (hvOld ha).elim
      · have hIdx : blockIndex blocks v < j := hPrefix.mp hPrefixV
        exact (mem_oldStage_iff (extendRunIndex a κ blocks hCover)
          (n+j) v).mpr (by omega)

/-- The kth proper fresh block is minimal over its actual old
prefix, with the same old graph fixed throughout the list. -/
theorem minimalStep_of_blockRun
    (G : GraphOn V) (a : Finset V)
    (blocks : List (Finset V))
    (hRun : G.toPredimension.IsMinimalBlockRun a blocks) :
    ∀ j : ℕ, j < blocks.length →
      G.toPredimension.IsMinimalStrongStep
        (a ∪ blockPrefix blocks j)
        (a ∪ blockPrefix blocks (j+1)) := by
  induction blocks generalizing a with
  | nil =>
      intro j hj
      simp at hj
  | cons B rest ih =>
      intro j hj
      change Disjoint a B ∧
        G.toPredimension.IsMinimalStrongStep a (a ∪ B) ∧
        G.toPredimension.IsMinimalBlockRun (a ∪ B) rest at hRun
      rcases hRun with ⟨_, hStep, hTail⟩
      cases j with
      | zero =>
          simpa [blockPrefix] using hStep
      | succ j =>
          have hBound : j < rest.length := by
            simp only [List.length_cons] at hj
            omega
          have hNext := ih (a ∪ B) hTail j hBound
          simpa [blockPrefix, Finset.union_assoc] using hNext

/-- Appending any finite list of disjoint minimal blocks preserves the
old indexed minimal-strong presentation, with one additional component
index for every new block. -/
theorem extendRunIndex_minimal_steps
    (G : GraphOn V)
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (hRun : G.toPredimension.IsMinimalBlockRun a blocks)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      (G.pullback (Subtype.val : {v : V // v ∈ a} → V)).toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) :
    ∀ k : ℕ, k < n + blocks.length →
      oldStage (extendRunIndex a κ blocks hCover) k =
        oldStage (extendRunIndex a κ blocks hCover) (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage (extendRunIndex a κ blocks hCover) k)
        (oldStage (extendRunIndex a κ blocks hCover) (k+1)) := by
  classical
  intro k hk
  by_cases hkOld : k < n
  · rcases hOld k hkOld with hEq | hMin
    · left
      rw [oldStage_extend_image a κ blocks hCover k (by omega),
        oldStage_extend_image a κ blocks hCover (k+1) (by omega),
        hEq]
    · right
      let H := G.pullback (Subtype.val : {v : V // v ∈ a} → V)
      have hMono : oldStage κ k ⊆ oldStage κ (k+1) := by
        intro u hu
        have hlt : (κ u).val < k := (mem_oldStage_iff κ k u).mp hu
        exact (mem_oldStage_iff κ (k+1) u).mpr (by omega)
      have hAdj : ∀ u v : {v : V // v ∈ a},
          H.adj u v ↔ G.adj u.val v.val := fun _ _ => Iff.rfl
      have hImage :
          G.toPredimension.IsMinimalStrongStep
            ((oldStage κ k).image (Subtype.val : {v : V // v ∈ a} → V))
            ((oldStage κ (k+1)).image (Subtype.val : {v : V // v ∈ a} → V)) :=
        (H.minimalStrongStep_image_iff G
          (Subtype.val : {v : V // v ∈ a} → V)
          Subtype.val_injective hAdj
          (oldStage κ k) (oldStage κ (k+1)) hMono).mpr hMin
      rw [← oldStage_extend_image a κ blocks hCover k (by omega),
        ← oldStage_extend_image a κ blocks hCover (k+1) (by omega)] at hImage
      exact hImage
  · let j := k-n
    have hj : j < blocks.length := by omega
    have hk : k = n+j := by omega
    right
    have hMin := minimalStep_of_blockRun G a blocks hRun j hj
    rw [hk, oldStage_extend_later a κ blocks hCover j (by omega),
      oldStage_extend_later a κ blocks hCover (j+1) (by omega)]
    exact hMin

/-- Changing the finite index bound from n to n+m, with no new
vertices, does not change the full backward-reachability closure. -/
theorem canonicalValue_castAdd
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphOn W) (κ : W → Fin n) (m : ℕ) (u : W) :
    canonicalValue H (fun v => (κ v).castAdd m) u =
      canonicalValue H κ u := by
  induction m with
  | zero =>
      have hMap : (fun v => (κ v).castAdd 0) = κ := by
        funext v
        apply Fin.ext
        rfl
      rw [hMap]
  | succ m ih =>
      have hMap :
          (fun v => (κ v).castAdd (m+1)) =
          (fun v => ((κ v).castAdd m).castSucc) := by
        funext v
        apply Fin.ext
        rfl
      rw [hMap, canonicalValue_castSucc H (fun v => (κ v).castAdd m) u]
      exact ih

/-- The full canonical C0 unary value of every old vertex is
literally unchanged by an arbitrary finite list of minimal new
components, not merely by one component at a time. -/
theorem canonicalValue_extendRun_old
    (G : GraphOn V)
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (blocks : List (Finset V))
    (hCover : Predimension.blockRunEnd a blocks = Finset.univ)
    (u : {v : V // v ∈ a}) :
    canonicalValue G (extendRunIndex a κ blocks hCover) u.val =
      (canonicalValue
        (G.pullback (Subtype.val : {v : V // v ∈ a} → V))
        κ u).image (Subtype.val : {v : V // v ∈ a} → V) := by
  classical
  have hClosed : G.IsClosedUnderValues
      (canonicalValue G (extendRunIndex a κ blocks hCover)) a := by
    have hPref :=
      canonicalValue_oldStage_closed G
        (extendRunIndex a κ blocks hCover) n
    rw [oldStage_extend_old a κ blocks hCover] at hPref
    exact hPref
  have hRestr := canonicalValue_restrict_image G
    (extendRunIndex a κ blocks hCover) a hClosed u
  have hIndex : restrictIndex (extendRunIndex a κ blocks hCover) a =
      (fun v : {v : V // v ∈ a} =>
        (κ v).castAdd blocks.length) := by
    funext v
    apply Fin.ext
    exact extendRunIndex_old a κ blocks hCover v
  rw [hIndex] at hRestr
  rw [canonicalValue_castAdd] at hRestr
  exact hRestr.symm

/-- Full finite graph-to-functional lifting for every finite strong
inclusion a≤V: a canonical minimal-strong presentation on the old
induced graph extends to a canonical presentation on all of V,
preserving all complete old unary values exactly. -/
theorem exists_canonical_extension_of_strong
    (G : GraphOn V) (a : Finset V)
    (κ : {v : V // v ∈ a} → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      (G.pullback (Subtype.val : {v : V // v ∈ a} → V)).toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (hStrong : G.toPredimension.IsStrong a Finset.univ) :
    ∃ (m : ℕ) (κFinal : V → Fin m),
      (∀ k : ℕ, k < m →
        oldStage κFinal k = oldStage κFinal (k+1) ∨
        G.toPredimension.IsMinimalStrongStep
          (oldStage κFinal k) (oldStage κFinal (k+1))) ∧
      (∀ u : {v : V // v ∈ a},
        canonicalValue G κFinal u.val =
          (canonicalValue
            (G.pullback (Subtype.val : {v : V // v ∈ a} → V))
            κ u).image (Subtype.val : {v : V // v ∈ a} → V)) := by
  obtain ⟨blocks, hRun, hCover⟩ :=
    G.toPredimension.exists_minimalBlockRun_of_strong hStrong
  refine ⟨n+blocks.length,
    extendRunIndex a κ blocks hCover,
    extendRunIndex_minimal_steps G a κ blocks hCover hRun hOld, ?_⟩
  intro u
  exact canonicalValue_extendRun_old G a κ blocks hCover u

end FiniteC0
end BigHrushovski
