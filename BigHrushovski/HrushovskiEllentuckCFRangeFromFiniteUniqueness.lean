import BigHrushovski.HrushovskiEllentuckFiniteLiftRangeCriterion
import BigHrushovski.HrushovskiEllentuckCFInverseFiniteLifts

/-!
# Reduction of the actual C_F copy-range equation to finite uniqueness

The abstract range criterion requires four separate finite inputs:
inclusion of a generated closure, composition with the ambient map,
uniqueness from level assignments, and existence of inverse finite
lifts. For the actual C_F birth carrier, the first, second and
fourth inputs can be discharged using existing structural results
and the inverse-lift existence theorem.

The only remaining hypothesis is uniqueness of genuine *ordered*
finite b-functional embeddings of each complete one-generated
closure with the same birth-level assignments. This is precisely
the finite rigidity problem now being developed in Track B.

No result here proves that finite uniqueness hypothesis, constructs
a global lift, or identifies the copy space with increasing sequences.
The theorem is a concrete reduction rather than a proof of the full
Section 6 Ellentuck theorem.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- A genuine finite embedding in the ordered auxiliary b-language.
It preserves the induced graph (including nonedges), the *complete*
finite unary values, the birth-level preorder and the canonical order.
The source is a finite subtype; no map on the rest of the countable
carrier is supplied or assumed. -/
def IsFiniteOrderedBEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K) : Prop :=
  Function.Injective e ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    (countableGraph F K).adj x.val y.val ↔
      (countableGraph F K).adj (e x) (e y)) ∧
  (∀ x : SupportCarrier (Vertex F K) s,
    (finiteSourceBirthBValue F K s x).image e =
      birthBValue F K (e x)) ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    BirthLevelLe F K x.val y.val ↔
      BirthLevelLe F K (e x) (e y)) ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    canonicalBirthLt F K x.val y.val ↔
      canonicalBirthLt F K (e x) (e y))

/-- Literal inclusion of any finite b-closed source is an embedding
of its complete finite restricted function values. -/
theorem finiteOrderedBEmbedding_inclusion
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) :
    IsFiniteOrderedBEmbedding F K s
      (fun x : SupportCarrier (Vertex F K) s => x.val) := by
  refine ⟨Subtype.val_injective, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Iff.rfl
  · intro x
    exact finiteSourceBirthBValue_image F K s hs x
  · intro x y
    exact Iff.rfl
  · intro x y
    exact Iff.rfl

/-- Composing a genuine finite b-embedding with an ambient ordered
b-embedding gives a genuine finite b-embedding on the SAME source.
The proof uses the full b-value equation, rather than assuming that
the ambient map can be restricted to a convenient finite target. -/
theorem finiteOrderedBEmbedding_comp_global
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (he : IsFiniteOrderedBEmbedding F K s e)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hB : ∀ u : Vertex F K,
      (birthBValue F K u).image f = birthBValue F K (f u))
    (hPreorder : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : ∀ u v : Vertex F K,
      canonicalBirthLt F K u v ↔ canonicalBirthLt F K (f u) (f v)) :
    IsFiniteOrderedBEmbedding F K s (fun x => f (e x)) := by
  classical
  obtain ⟨heInj, heAdj, heB, hePreorder, heOrder⟩ := he
  refine ⟨hf.comp heInj, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (heAdj x y).trans (hAdj (e x) (e y))
  · intro x
    calc
      (finiteSourceBirthBValue F K s x).image (fun w => f (e w)) =
          ((finiteSourceBirthBValue F K s x).image e).image f := by
            rw [Finset.image_image]
      _ = (birthBValue F K (e x)).image f := by rw [heB x]
      _ = birthBValue F K (f (e x)) := hB (e x)
  · intro x y
    exact (hePreorder x y).trans (hPreorder (e x) (e y))
  · intro x y
    exact (heOrder x y).trans (hOrder (e x) (e y))

/-- The concrete C_F range equation from *one* outstanding
finite-uniqueness hypothesis. The required inverse finite lifts
are genuine ordered b-embeddings built by Track B, not arbitrary
maps carrying only vertex birth labels.

The uniqueness hypothesis is local to the complete generated
closure of each single vertex, and compares all its vertices.
It is not asserted to have been proved. -/
theorem birthEmbedding_range_eq_levelDomain_of_finite_uniqueness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) (h : ℕ → ℕ)
    (hh : StrictMono h)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hB : ∀ u : Vertex F K,
      (birthBValue F K u).image f = birthBValue F K (f u))
    (hPreorder : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : ∀ u v : Vertex F K,
      canonicalBirthLt F K u v ↔ canonicalBirthLt F K (f u) (f v))
    (hBirth : ∀ u : Vertex F K, (f u).1 = h u.1)
    (hUnique :
      ∀ v : Vertex F K,
        ∀ (g k : SupportCarrier (Vertex F K)
            (birthSingletonClosure F K v) → Vertex F K),
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) g →
          IsFiniteOrderedBEmbedding F K (birthSingletonClosure F K v) k →
          (∀ x, (g x).1 = (k x).1) →
          g = k) :
    (Set.range f : Set (Vertex F K)) =
      birthLevelDomain F K (Set.range h) := by
  classical
  exact Ellentuck.range_eq_supportDomain_of_finite_lifts
    (birthSingletonClosure F K)
    (fun v : Vertex F K => v.1) f h
    (birthSingletonClosure_self F K)
    (birthSingletonClosure_image_of_bValues F K f hB)
    hBirth
    (fun s e => IsFiniteOrderedBEmbedding F K s e)
    (by
      intro v
      exact finiteOrderedBEmbedding_inclusion F K
        (birthSingletonClosure F K v)
        (birthGeneratedClosure_closed F K
          ({v} : Finset (Vertex F K))))
    (by
      intro v g hg
      exact finiteOrderedBEmbedding_comp_global F K
        (birthSingletonClosure F K v) g hg
        f hf hAdj hB hPreorder hOrder)
    (by
      intro v g k hg hk hLevel
      exact hUnique v g k hg hk hLevel)
    (by
      intro v hv
      let s : Finset (Vertex F K) := birthSingletonClosure F K v
      have hs : IsBirthBlockClosed F K s :=
        birthGeneratedClosure_closed F K ({v} : Finset (Vertex F K))
      have hRange : ∀ w ∈ s, w.1 ∈ Set.range h := by
        intro w hw
        exact hv w.1
          ((birthLevelSupport_mem_iff F K v w.1).2 ⟨w, hw, rfl⟩)
      obtain ⟨g, hgInj, hgAdj, hgB, hgInv, hgPre, hgOrder⟩ :=
        finiteClosed_inverseLevelLift_exists F K s hs h hh hRange
      exact ⟨g, ⟨hgInj, hgAdj, hgB, hgPre, hgOrder⟩, hgInv⟩)

end BigHrushovski.CFCoherentTower
