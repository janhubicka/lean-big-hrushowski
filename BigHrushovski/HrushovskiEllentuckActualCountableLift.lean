import BigHrushovski.HrushovskiEllentuckCountableLiftFromFiniteUniqueness
import BigHrushovski.CFArbitraryFiniteUniqueness

/-!
# Unconditional countable C_F level lifts in the ordered b-language

The genuine finite uniqueness theorem has now been proved in Track B:
two arbitrary finite ordered b-embeddings of a b-closed source with
the same target birth level at every vertex are equal. Thus the sole
hypothesis in the preceding Track E countable reduction can be
discharged. No additional coherence or infinite extension principle
is required.

For each strictly increasing level map h, there is a unique global
ordered b-embedding f with level action h; its range is the
complete-support domain determined by range(h).

This proves the auxiliary ordered b-embedding statement. The
identification with all embeddings in the paper's partial (R,H)
language and the topological Ramsey-space axioms are separate.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- The exact Track B arbitrary finite uniqueness theorem, repackaged
for the common Track E finite ordered b-embedding predicate. -/
theorem finiteOrderedBEmbedding_unique_of_birthLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e g : SupportCarrier (Vertex F K) s → Vertex F K)
    (he : IsFiniteOrderedBEmbedding F K s e)
    (hg : IsFiniteOrderedBEmbedding F K s g)
    (hLevel : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = (g x).1) :
    e = g := by
  rcases he with ⟨heInj, heAdj, heB, hePre, heOrder⟩
  rcases hg with ⟨hgInj, hgAdj, hgB, hgPre, hgOrder⟩
  exact arbitraryFiniteEmbedding_unique_of_targetLevels
    F K s hs e g
    heInj hgInj heAdj hgAdj heB hgB
    hePre hgPre heOrder hgOrder hLevel

/-- The unique-embedding hypothesis of the countable gluing and
range criteria is already a verified theorem of the finite C_F
construction. No new axiom is introduced. -/
theorem singletonClosure_finiteOrderedBEmbedding_unique
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    ∀ v : Vertex F K,
      ∀ (e g : SupportCarrier (Vertex F K)
          (birthSingletonClosure F K v) → Vertex F K),
        IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) e →
        IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
        (∀ x, (e x).1 = (g x).1) →
        e = g := by
  intro v e g he hg hLevel
  exact finiteOrderedBEmbedding_unique_of_birthLevels
    F K (birthSingletonClosure F K v)
    (birthGeneratedClosure_closed F K
      ({v} : Finset (Vertex F K)))
    e g he hg hLevel

/-- A global ordered b-embedding with a prescribed level action.
All values are the entire actual ambient b-values, not values of
an arbitrarily restricted unary operation. -/
def IsGlobalOrderedBEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) : Prop :=
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
  (∀ v : Vertex F K, (f v).1 = h v.1)

/-- Actual countable existence, uniqueness and exact range recognition
in the auxiliary ordered b-language. The only new step is applying
the already certified Track B finite uniqueness theorem to the
conditional Track E gluing and range results. -/
theorem existsUnique_globalOrderedBEmbedding_with_range
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) :
    ∃! f : Vertex F K → Vertex F K,
      IsGlobalOrderedBEmbedding F K h f ∧
        Set.range f = birthLevelDomain F K (Set.range h) := by
  have hUnique := singletonClosure_finiteOrderedBEmbedding_unique F K
  obtain ⟨f, hfInj, hfAdj, hfB, hfPre, hfOrder, hfBirth, hRange⟩ :=
    exists_globalOrderedBEmbedding_range_eq_of_singleton_uniqueness
      F K h hh hUnique
  refine ⟨f, ⟨⟨hfInj, hfAdj, hfB, hfPre, hfOrder, hfBirth⟩, hRange⟩, ?_⟩
  intro g hg
  obtain ⟨⟨hgInj, hgAdj, hgB, hgPre, hgOrder, hgBirth⟩, _⟩ := hg
  exact globalOrderedBEmbedding_unique_of_singleton_uniqueness
    F K h hh hUnique g f
    hgInj hfInj hgAdj hfAdj hgB hfB
    hgOrder hfOrder hgBirth hfBirth

end BigHrushovski.CFCoherentTower
