import BigHrushovski.HrushovskiEllentuckCFRangeFromFiniteUniqueness

/-!
# Gluing coherent embeddings of finite C_F birth stages

Each actual birth stage U_n is finite, and all its complete auxiliary
b-values lie within U_n. A family of genuine ordered b-embeddings
of these stages which agrees on overlaps therefore determines a
genuine embedding of the entire countable birth presentation.

This lemma isolates the countable passage from the finite
lifting construction. It does NOT assert that the prescribed
finite lifts are coherent: coherence will follow from the
remaining finite uniqueness theorem, or from a direct proof
that the finite construction is compatible with restriction.

The resulting map preserves the induced graph, full b-values,
the canonical order, and the level action. In particular there
is no compactness or new Fraisse extension assumption in this step.
-/

namespace BigHrushovski.CFCoherentTower

/-- A choice of maps on the exact finite birth-stage images. -/
abbrev StageEmbeddingFamily (F : ℕ → ℝ) (K : ℕ → ℕ) :=
  (n : ℕ) → SupportCarrier (Vertex F K) (stageImage F K n) → Vertex F K

/-- Compatibility of stage maps on every pair of nested actual
finite stages, with no choice of a second abstract copy. -/
def StageEmbeddingFamily.Coherent
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (e : StageEmbeddingFamily F K) : Prop :=
  ∀ (n m : ℕ) (hnm : n ≤ m)
    (v : Vertex F K)
    (hvn : v ∈ stageImage F K n)
    (hvm : v ∈ stageImage F K m),
    e n ⟨v, hvn⟩ = e m ⟨v, hvm⟩

/-- Evaluate each vertex at the first finite stage containing it. -/
noncomputable def gluedStageEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (e : StageEmbeddingFamily F K)
    (v : Vertex F K) : Vertex F K :=
  e (v.1 + 1)
    ⟨v, (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).mpr
      (Nat.lt_succ_self v.1)⟩

/-- On every original finite stage, the glued map is literally
the prescribed stage map, independently of the proof that a
vertex belongs to the stage. -/
theorem gluedStageEmbedding_eq_on_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (e : StageEmbeddingFamily F K)
    (hCoherent : StageEmbeddingFamily.Coherent F K e)
    (n : ℕ) (v : Vertex F K)
    (hv : v ∈ stageImage F K n) :
    gluedStageEmbedding F K e v = e n ⟨v, hv⟩ := by
  have hvFirst :
      v ∈ stageImage F K (v.1 + 1) :=
    (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).mpr
      (Nat.lt_succ_self v.1)
  have hle : v.1 + 1 ≤ n := by
    exact Nat.succ_le_iff.mpr
      ((mem_stageImage_iff_birth_lt F K n v).mp hv)
  exact hCoherent (v.1 + 1) n hle v hvFirst hv

/-- The exact countable lifting interface. Assuming genuinely
coherent finite ordered b-embeddings which act on birth levels by
the same h, their union is a global ordered b-embedding with
birth-level action h.

This establishes the infinite *gluing* step, not the existence
or uniqueness of the finite-compatible witness family. -/
theorem exists_globalOrderedBEmbedding_of_coherent_stages
    (F : ℕ → ℝ) (K : ℕ → ℕ) (h : ℕ → ℕ)
    (e : StageEmbeddingFamily F K)
    (hEmb : ∀ n, IsFiniteOrderedBEmbedding F K
      (stageImage F K n) (e n))
    (hLevel : ∀ n
      (x : SupportCarrier (Vertex F K) (stageImage F K n)),
        (e n x).1 = h x.val.1)
    (hCoherent : StageEmbeddingFamily.Coherent F K e) :
    ∃ f : Vertex F K → Vertex F K,
      Function.Injective f ∧
      (∀ u v : Vertex F K,
        (countableGraph F K).adj u v ↔
          (countableGraph F K).adj (f u) (f v)) ∧
      (∀ v : Vertex F K,
        (birthBValue F K v).image f = birthBValue F K (f v)) ∧
      (∀ u v : Vertex F K,
        BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v)) ∧
      (∀ u v : Vertex F K,
        canonicalBirthLt F K u v ↔ canonicalBirthLt F K (f u) (f v)) ∧
      (∀ v : Vertex F K, (f v).1 = h v.1) := by
  classical
  let f := gluedStageEmbedding F K e
  have hApply : ∀ n (v : Vertex F K)
      (hv : v ∈ stageImage F K n),
      f v = e n ⟨v, hv⟩ := by
    intro n v hv
    exact gluedStageEmbedding_eq_on_stage F K e hCoherent n v hv
  have hPair : ∀ u v : Vertex F K,
      ∃ n : ℕ,
        u ∈ stageImage F K n ∧ v ∈ stageImage F K n := by
    intro u v
    refine ⟨max u.1 v.1 + 1, ?_, ?_⟩
    · exact (mem_stageImage_iff_birth_lt F K _ u).mpr
        (Nat.lt_succ_of_le (Nat.le_max_left _ _))
    · exact (mem_stageImage_iff_birth_lt F K _ v).mpr
        (Nat.lt_succ_of_le (Nat.le_max_right _ _))
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨n, hu, hv⟩ := hPair u v
    obtain ⟨hi, _, _, _, _⟩ := hEmb n
    have hEq : e n ⟨u, hu⟩ = e n ⟨v, hv⟩ := by
      calc
        e n ⟨u, hu⟩ = f u := (hApply n u hu).symm
        _ = f v := huv
        _ = e n ⟨v, hv⟩ := hApply n v hv
    exact congrArg Subtype.val (hi hEq)
  · intro u v
    obtain ⟨n, hu, hv⟩ := hPair u v
    obtain ⟨_, hAdj, _, _, _⟩ := hEmb n
    rw [hApply n u hu, hApply n v hv]
    exact hAdj ⟨u, hu⟩ ⟨v, hv⟩
  · intro v
    let n := v.1 + 1
    have hv : v ∈ stageImage F K n :=
      (mem_stageImage_iff_birth_lt F K n v).mpr
        (Nat.lt_succ_self v.1)
    have hs : IsBirthBlockClosed F K (stageImage F K n) :=
      stageImage_birthBlockClosed F K n
    obtain ⟨_, _, hB, _, _⟩ := hEmb n
    have hVal : (finiteSourceBirthBValue F K
        (stageImage F K n) ⟨v, hv⟩).image Subtype.val =
        birthBValue F K v :=
      finiteSourceBirthBValue_image F K
        (stageImage F K n) hs ⟨v, hv⟩
    calc
      (birthBValue F K v).image f =
          ((finiteSourceBirthBValue F K
            (stageImage F K n) ⟨v, hv⟩).image Subtype.val).image f := by
              rw [hVal]
      _ = (finiteSourceBirthBValue F K
            (stageImage F K n) ⟨v, hv⟩).image (e n) := by
              rw [Finset.image_image]
              apply Finset.image_congr
              intro w hw
              exact hApply n w.val w.property
      _ = birthBValue F K (e n ⟨v, hv⟩) := hB ⟨v, hv⟩
      _ = birthBValue F K (f v) := by rw [hApply n v hv]
  · intro u v
    obtain ⟨n, hu, hv⟩ := hPair u v
    obtain ⟨_, _, _, hLe, _⟩ := hEmb n
    rw [hApply n u hu, hApply n v hv]
    exact hLe ⟨u, hu⟩ ⟨v, hv⟩
  · intro u v
    obtain ⟨n, hu, hv⟩ := hPair u v
    obtain ⟨_, _, _, _, hOrd⟩ := hEmb n
    rw [hApply n u hu, hApply n v hv]
    exact hOrd ⟨u, hu⟩ ⟨v, hv⟩
  · intro v
    have hv : v ∈ stageImage F K (v.1 + 1) :=
      (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).mpr
        (Nat.lt_succ_self v.1)
    calc
      (f v).1 = (e (v.1 + 1) ⟨v, hv⟩).1 := by
        rw [hApply (v.1 + 1) v hv]
      _ = h v.1 := hLevel (v.1 + 1) ⟨v, hv⟩

end BigHrushovski.CFCoherentTower
