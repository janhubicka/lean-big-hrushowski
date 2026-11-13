import BigHrushovski.HrushovskiEllentuckActualCountableLift
import BigHrushovski.CFCanonicalOrderEmbedding

/-!
# Countable ordered C_F embeddings in the b and (R,H) languages

The finite source-subtype equivalence between exact complete b-values
and the actual R-values and partial H-values works for arbitrary
b-closed source subsets, not only finite sets. Here we apply it to
the whole countable birth carrier.

Both embedding predicates explicitly preserve the canonical order,
the birth-level preorder and a prescribed level action. The theorem
therefore compares the same expanded ordered embedding notion in
the two languages. It does not assert that an arbitrary reduct
embedding recovers its level action automatically.

The countable unique b-lift theorem consequently supplies
existence, uniqueness, and the exact support-range formula in
this precise (R,H) embedding language, including reflection
of the domain of partial H.
-/

namespace BigHrushovski.CFCoherentTower

/-- Complete R(v) and H(S) transport for a global self-map,
including reflection of the domain where H is defined.
The source of the partial H-operation consists of finite
sets all of whose members are genuine birth roots. -/
def GlobalRHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) : Prop :=
  (∀ v : Vertex F K,
    (birthReachableRoots F K v).image f =
      birthReachableRoots F K (f v)) ∧
  (∀ s : Finset (Vertex F K),
    (∀ r ∈ s, IsBirthRoot F K r) →
    (birthDClosedHull F K s).image f =
      birthDClosedHull F K (s.image f)) ∧
  (∀ s : Finset (Vertex F K),
    (∀ r ∈ s, IsBirthRoot F K r) ↔
      (∀ r ∈ s.image f, IsBirthRoot F K r))

/-- In the actual countable birth structure, exact complete b-value
transport is equivalent to transport of the genuine R-values and
partial H-values with domain reflection, for a map preserving
the induced graph and the two canonical orders. -/
theorem globalBValues_iff_RHValues_of_canonicalOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hPre : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : ∀ u v : Vertex F K,
      canonicalBirthLt F K u v ↔
        canonicalBirthLt F K (f u) (f v)) :
    (∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      GlobalRHValues F K f := by
  let X : Set (Vertex F K) := Set.univ
  let e : {v : Vertex F K // v ∈ X} → Vertex F K :=
    fun v => f v.val
  have hX : IsBirthBlockClosedSet F K X := by
    intro n r i hv
    exact ⟨(fun j => Set.mem_univ _),
      (fun u hu => Set.mem_univ _)⟩
  have heInj : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    exact hf huv
  have heAdj : ∀ u v : {v : Vertex F K // v ∈ X},
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (e u) (e v) := by
    intro u v
    exact hAdj u.val v.val
  have hePre : ∀ u v : {v : Vertex F K // v ∈ X},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v) := by
    intro u v
    exact hPre u.val v.val
  have heOrder : ∀ u v : {v : Vertex F K // v ∈ X},
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (e u) (e v) := by
    intro u v
    exact hOrder u.val v.val
  have hEquivalence :=
    literalClosedSource_bValues_iff_RHValues_of_canonicalOrder
      F K X hX e heInj heAdj hePre heOrder
  simpa [X, e, extendClosedSourceMap, GlobalRHValues] using hEquivalence

/-- A genuine countable embedding in the expanded ordered
(R,H) language with a specified birth-level action. The
domain of partial H must be preserved AND reflected. -/
def IsGlobalOrderedRHEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) : Prop :=
  Function.Injective f ∧
  (∀ u v : Vertex F K,
    (countableGraph F K).adj u v ↔
      (countableGraph F K).adj (f u) (f v)) ∧
  (∀ u v : Vertex F K,
    BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v)) ∧
  (∀ u v : Vertex F K,
    canonicalBirthLt F K u v ↔
      canonicalBirthLt F K (f u) (f v)) ∧
  (∀ v : Vertex F K, (f v).1 = h v.1) ∧
  GlobalRHValues F K f

/-- Equivalence of the two exact countable functional embedding
predicates, without any finite or countable lift hypothesis. -/
theorem isGlobalOrderedBEmbedding_iff_RH
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (f : Vertex F K → Vertex F K) :
    IsGlobalOrderedBEmbedding F K h f ↔
      IsGlobalOrderedRHEmbedding F K h f := by
  constructor
  · intro hb
    obtain ⟨hf, hAdj, hB, hPre, hOrder, hBirth⟩ := hb
    have hRH : GlobalRHValues F K f :=
      (globalBValues_iff_RHValues_of_canonicalOrder
        F K f hf hAdj hPre hOrder).mp hB
    exact ⟨hf, hAdj, hPre, hOrder, hBirth, hRH⟩
  · intro hRH
    obtain ⟨hf, hAdj, hPre, hOrder, hBirth, hValues⟩ := hRH
    have hB := (globalBValues_iff_RHValues_of_canonicalOrder
      F K f hf hAdj hPre hOrder).mpr hValues
    exact ⟨hf, hAdj, hB, hPre, hOrder, hBirth⟩

/-- Existence, uniqueness, and complete-support range recognition
for global ordered (R,H)-embeddings with prescribed strictly
increasing birth-level action, including the partial H domain.
No finite uniqueness or coherence assumption remains. -/
theorem existsUnique_globalOrderedRHEmbedding_with_range
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) :
    ∃! f : Vertex F K → Vertex F K,
      IsGlobalOrderedRHEmbedding F K h f ∧
        Set.range f = birthLevelDomain F K (Set.range h) := by
  obtain ⟨f, hf, hUnique⟩ :=
    existsUnique_globalOrderedBEmbedding_with_range F K h hh
  refine ⟨f, ⟨(isGlobalOrderedBEmbedding_iff_RH
    F K h f).mp hf.1, hf.2⟩, ?_⟩
  intro g hg
  exact hUnique g
    ⟨(isGlobalOrderedBEmbedding_iff_RH F K h g).mpr hg.1, hg.2⟩

end BigHrushovski.CFCoherentTower
