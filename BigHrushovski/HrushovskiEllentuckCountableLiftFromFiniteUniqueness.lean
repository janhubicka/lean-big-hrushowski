import BigHrushovski.HrushovskiEllentuckFiniteRestriction

/-!
# Countable C_F level lifts from one finite uniqueness theorem

Track B's prescribed finite lifting theorem supplies an ordered
b-embedding of every actual finite birth stage at any strictly
increasing target assignment. The preceding restriction theorem
turns uniqueness on complete singleton-generated closures into
uniqueness on whole finite stages. Consequently independently
chosen finite lifts MUST agree on their overlaps.

The coherent-stage gluing theorem then gives a global ordered
b-embedding with the prescribed level action. Together with the
conditional complete-support range formula, this proves existence,
the exact range description, and uniqueness of the global lift
conditional on only the SAME finite singleton-closure uniqueness
property. There is no second coherence hypothesis.

No claim is made that Track B has proved that finite uniqueness
property yet; that is the sole remaining mathematical hypothesis.
-/

namespace BigHrushovski.CFCoherentTower

/-- Every literal finite birth stage admits a genuine ordered
b-embedding realizing a strictly increasing assignment of source
birth levels. This is the already certified finite prescribed-lift
existence theorem, packaged for the coherent-stage argument. -/
theorem finiteOrderedStageLift_exists
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (n : ℕ) :
    ∃ e : SupportCarrier (Vertex F K) (stageImage F K n) → Vertex F K,
      IsFiniteOrderedBEmbedding F K (stageImage F K n) e ∧
      (∀ x, (e x).1 = h x.val.1) := by
  have hStrict :
      StrictOnRepresented F K (stageImage F K n) h := by
    intro i hi j hj hij
    exact hh hij
  obtain ⟨e, heInj, heAdj, heB, heBirth, hePre, heOrder⟩ :=
    finiteSourcePrescribedLift_exists_ordered
      F K (stageImage F K n)
      (stageImage_birthBlockClosed F K n) h hStrict
  exact ⟨e, ⟨heInj, heAdj, heB, hePre, heOrder⟩, heBirth⟩

/-- Choose one finite lift of every actual finite stage.
No coherence is asserted by the definition. -/
noncomputable def chosenFiniteStageLifts
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) :
    StageEmbeddingFamily F K :=
  fun n => Classical.choose (finiteOrderedStageLift_exists F K h hh n)

theorem chosenFiniteStageLifts_embeds
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (n : ℕ) :
    IsFiniteOrderedBEmbedding F K (stageImage F K n)
      (chosenFiniteStageLifts F K h hh n) :=
  (Classical.choose_spec (finiteOrderedStageLift_exists F K h hh n)).1

theorem chosenFiniteStageLifts_birthLevel
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (n : ℕ)
    (x : SupportCarrier (Vertex F K) (stageImage F K n)) :
    (chosenFiniteStageLifts F K h hh n x).1 = h x.val.1 :=
  (Classical.choose_spec (finiteOrderedStageLift_exists F K h hh n)).2 x

/-- Uniqueness on complete one-generated closures forces all
finite prescribed stage lifts to agree on nested stages.
No additional assumption about coherence is introduced. -/
theorem chosenFiniteStageLifts_coherent_of_singleton_uniqueness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hUnique :
      ∀ v : Vertex F K,
        ∀ (g k : SupportCarrier (Vertex F K)
            (birthSingletonClosure F K v) → Vertex F K),
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) k →
          (∀ x, (g x).1 = (k x).1) →
          g = k) :
    StageEmbeddingFamily.Coherent F K
      (chosenFiniteStageLifts F K h hh) := by
  classical
  let e := chosenFiniteStageLifts F K h hh
  intro n m hnm v hvn hvm
  have hst : stageImage F K n ⊆ stageImage F K m :=
    stageImage_mono F K hnm
  let g : SupportCarrier (Vertex F K) (stageImage F K n) → Vertex F K :=
    fun x => e m ⟨x.val, hst x.property⟩
  have hnEmb : IsFiniteOrderedBEmbedding F K
      (stageImage F K n) (e n) :=
    chosenFiniteStageLifts_embeds F K h hh n
  have hmEmb : IsFiniteOrderedBEmbedding F K
      (stageImage F K m) (e m) :=
    chosenFiniteStageLifts_embeds F K h hh m
  have hgEmb : IsFiniteOrderedBEmbedding F K (stageImage F K n) g :=
    finiteOrderedBEmbedding_restrict F K
      (stageImage F K n) (stageImage F K m)
      (stageImage_birthBlockClosed F K n) hst (e m) hmEmb
  have hSame : ∀ x : SupportCarrier (Vertex F K) (stageImage F K n),
      (e n x).1 = (g x).1 := by
    intro x
    calc
      (e n x).1 = h x.val.1 :=
        chosenFiniteStageLifts_birthLevel F K h hh n x
      _ = (g x).1 :=
        (chosenFiniteStageLifts_birthLevel F K h hh m
          ⟨x.val, hst x.property⟩).symm
  have heq : e n = g :=
    finiteStage_uniqueness_of_singleton_uniqueness
      F K hUnique n (e n) g hnEmb hgEmb hSame
  have hvEq : e n ⟨v, hvn⟩ =
      e m ⟨v, hst hvn⟩ := by
    exact congrFun heq ⟨v, hvn⟩
  have hProof : (⟨v, hst hvn⟩ :
      SupportCarrier (Vertex F K) (stageImage F K m)) = ⟨v, hvm⟩ :=
    Subtype.ext rfl
  exact hvEq.trans (congrArg (e m) hProof)

/-- The single local finite uniqueness theorem is enough to
construct a genuine countable ordered b-embedding for EVERY
strictly increasing level assignment h. The proof needs no
additional stage coherence or compactness hypothesis. -/
theorem exists_globalOrderedBEmbedding_of_singleton_uniqueness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hUnique :
      ∀ v : Vertex F K,
        ∀ (g k : SupportCarrier (Vertex F K)
            (birthSingletonClosure F K v) → Vertex F K),
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) k →
          (∀ x, (g x).1 = (k x).1) →
          g = k) :
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
  let e := chosenFiniteStageLifts F K h hh
  exact exists_globalOrderedBEmbedding_of_coherent_stages
    F K h e
    (chosenFiniteStageLifts_embeds F K h hh)
    (chosenFiniteStageLifts_birthLevel F K h hh)
    (chosenFiniteStageLifts_coherent_of_singleton_uniqueness
      F K h hh hUnique)

/-- Combining the countable gluing theorem with the exact
range criterion gives a global lift whose range is precisely
the full-support domain over the image levels. The only
unproved input remains finite singleton-closure uniqueness. -/
theorem exists_globalOrderedBEmbedding_range_eq_of_singleton_uniqueness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hUnique :
      ∀ v : Vertex F K,
        ∀ (g k : SupportCarrier (Vertex F K)
            (birthSingletonClosure F K v) → Vertex F K),
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) k →
          (∀ x, (g x).1 = (k x).1) →
          g = k) :
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
      (∀ v : Vertex F K, (f v).1 = h v.1) ∧
      Set.range f = birthLevelDomain F K (Set.range h) := by
  obtain ⟨f, hf, hAdj, hB, hPre, hOrder, hBirth⟩ :=
    exists_globalOrderedBEmbedding_of_singleton_uniqueness
      F K h hh hUnique
  refine ⟨f, hf, hAdj, hB, hPre, hOrder, hBirth, ?_⟩
  exact birthEmbedding_range_eq_levelDomain_of_finite_uniqueness
    F K f h hh hf hAdj hB hOrder hBirth hUnique

end BigHrushovski.CFCoherentTower
