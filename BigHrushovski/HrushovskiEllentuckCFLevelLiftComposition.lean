import BigHrushovski.HrushovskiEllentuckActualCountableLift

/-!
# Composition of the canonical countable C_F level lifts

The actual finite uniqueness theorem gives a unique global ordered
b-embedding for each strictly increasing level map. The exact
definition below chooses that unique embedding. Composition
preserves the full auxiliary b-values, induced graph and orders,
so uniqueness forces the lift of a composite level map to be
the composite of its lifts.

This is a composition law for the canonical b-lifts. It is not yet
a classification of every embedding in the paper's partial (R,H)
language, nor a claim that every ordered b-embedding has a
level action represented by an increasing map of all naturals.
-/

namespace BigHrushovski.CFCoherentTower

/-- Exact transport of the complete ordered b-structure under
composition of genuine countable embeddings. -/
theorem isGlobalOrderedBEmbedding_comp
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h k : ℕ → ℕ)
    (f g : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedBEmbedding F K h f)
    (hg : IsGlobalOrderedBEmbedding F K k g) :
    IsGlobalOrderedBEmbedding F K (k ∘ h) (g ∘ f) := by
  classical
  obtain ⟨hfInj, hfAdj, hfB, hfPre, hfOrder, hfBirth⟩ := hf
  obtain ⟨hgInj, hgAdj, hgB, hgPre, hgOrder, hgBirth⟩ := hg
  refine ⟨hgInj.comp hfInj, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (hfAdj u v).trans (hgAdj (f u) (f v))
  · intro v
    calc
      (birthBValue F K v).image (g ∘ f) =
          ((birthBValue F K v).image f).image g := by
            rw [Finset.image_image]
      _ = (birthBValue F K (f v)).image g := by
        rw [hfB v]
      _ = birthBValue F K (g (f v)) := hgB (f v)
  · intro u v
    exact (hfPre u v).trans (hgPre (f u) (f v))
  · intro u v
    exact (hfOrder u v).trans (hgOrder (f u) (f v))
  · intro v
    change (g (f v)).1 = k (h v.1)
    rw [hgBirth (f v), hfBirth v]

/-- The identity function is a genuine global ordered b-embedding
with identity birth-level action. -/
theorem isGlobalOrderedBEmbedding_id
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    IsGlobalOrderedBEmbedding F K
      (fun n : ℕ => n)
      (fun v : Vertex F K => v) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    exact h
  · intro u v
    exact Iff.rfl
  · intro v
    simp
  · intro u v
    exact Iff.rfl
  · intro u v
    exact Iff.rfl
  · intro v
    rfl

/-- A canonical total lift of any strictly increasing action on
the birth levels, selected by the verified existence-and-uniqueness
theorem. The choice is mathematically unique. -/
noncomputable def canonicalOrderedBLevelLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) :
    Vertex F K → Vertex F K :=
  Classical.choose
    (existsUnique_globalOrderedBEmbedding_with_range F K h hh)

/-- The chosen lift is a genuine embedding and has the exact
complete-support range. -/
theorem canonicalOrderedBLevelLift_spec
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) :
    IsGlobalOrderedBEmbedding F K h
      (canonicalOrderedBLevelLift F K h hh) ∧
    Set.range (canonicalOrderedBLevelLift F K h hh) =
      birthLevelDomain F K (Set.range h) :=
  (Classical.choose_spec
    (existsUnique_globalOrderedBEmbedding_with_range F K h hh)).1

/-- Any other genuine ordered b-lift with the same level action
equals the canonical lift. No assumption about its range is needed;
range equality follows from the already proved finite uniqueness. -/
theorem canonicalOrderedBLevelLift_unique
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (f : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedBEmbedding F K h f) :
    f = canonicalOrderedBLevelLift F K h hh := by
  have hCanon :=
    (canonicalOrderedBLevelLift_spec F K h hh).1
  obtain ⟨hfInj, hfAdj, hfB, _, hfOrder, hfBirth⟩ := hf
  obtain ⟨hgInj, hgAdj, hgB, _, hgOrder, hgBirth⟩ := hCanon
  exact globalOrderedBEmbedding_unique_of_singleton_uniqueness
    F K h hh (singletonClosure_finiteOrderedBEmbedding_unique F K)
    f (canonicalOrderedBLevelLift F K h hh)
    hfInj hgInj hfAdj hgAdj hfB hgB
    hfOrder hgOrder hfBirth hgBirth

/-- Lifting the composite of two increasing level maps is exactly
composition of their canonical ordered b-lifts. -/
theorem canonicalOrderedBLevelLift_comp
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h k : ℕ → ℕ) (hh : StrictMono h) (hk : StrictMono k) :
    canonicalOrderedBLevelLift F K (k ∘ h) (hk.comp hh) =
      (canonicalOrderedBLevelLift F K k hk) ∘
        (canonicalOrderedBLevelLift F K h hh) := by
  have hComposite : IsGlobalOrderedBEmbedding F K (k ∘ h)
      ((canonicalOrderedBLevelLift F K k hk) ∘
        (canonicalOrderedBLevelLift F K h hh)) :=
    isGlobalOrderedBEmbedding_comp F K h k
      (canonicalOrderedBLevelLift F K h hh)
      (canonicalOrderedBLevelLift F K k hk)
      (canonicalOrderedBLevelLift_spec F K h hh).1
      (canonicalOrderedBLevelLift_spec F K k hk).1
  exact (canonicalOrderedBLevelLift_unique F K (k ∘ h)
    (hk.comp hh) _ hComposite).symm

/-- The lift of the identity level action is the identity
on the entire actual countable birth carrier. -/
theorem canonicalOrderedBLevelLift_id
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    canonicalOrderedBLevelLift F K
      (fun n : ℕ => n)
      (by intro a b hab; exact hab) =
      (fun v : Vertex F K => v) := by
  have hId : IsGlobalOrderedBEmbedding F K
      (fun n : ℕ => n) (fun v : Vertex F K => v) :=
    isGlobalOrderedBEmbedding_id F K
  exact (canonicalOrderedBLevelLift_unique F K
    (fun n : ℕ => n)
    (by intro a b hab; exact hab)
    (fun v : Vertex F K => v) hId).symm

end BigHrushovski.CFCoherentTower
