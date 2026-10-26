import BigHrushovski.CFClosedSourceEmbeddingValues

/-!
# Literal source-subtype interface for C_F functional embeddings

The preceding theorem compares complete b- and R,H-values on an
arbitrary closed source X, using a function on the whole vertex
carrier whose hypotheses are required only on X. It does not
postulate that this function is a global embedding.

Here the actual embedding has type
    {v : Vertex F K // v ∈ X} → Vertex F K.
Extend this map to the ambient vertex type by fixing every vertex
outside X. This extension is *not* claimed to be an embedding
outside X. All inducedness, injectivity and order hypotheses
are transported only from pairs of elements of the source subtype,
and the source-local equivalence theorem then applies.

This works for the empty source as well. No auxiliary source
vertex or ambient inhabitance assumption is needed.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- An arbitrary extension of a literal partial source map,
by the identity map outside the source. No embedding
property is claimed outside X. -/
noncomputable def extendClosedSourceMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (e : {v : Vertex F K // v ∈ X} → Vertex F K) :
    Vertex F K → Vertex F K := by
  classical
  exact fun v =>
    if hv : v ∈ X then e ⟨v, hv⟩ else v

/-- The source extension agrees literally with the original
embedding on every vertex of its domain. -/
theorem extendClosedSourceMap_apply
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (e : {v : Vertex F K // v ∈ X} → Vertex F K)
    (v : Vertex F K) (hv : v ∈ X) :
    extendClosedSourceMap F K X e v = e ⟨v, hv⟩ := by
  simp [extendClosedSourceMap, hv]

/-- Exact b/R,H value equivalence for a literal embedding
whose type has an arbitrary b-closed source subtype.

All map hypotheses are stated directly on elements of that
subtype; no extension of the map to a globally induced
self-embedding is assumed or used. The extension by a constant
is merely a device for applying the already verified source-local
value theorem, which ignores all vertices outside X.

The internal block order is the chosen order on Fin n fresh
ordinals, and the level preorder is the enumeration-level
relation in the manuscript. The empty source is included
without a special case or an inhabitance assumption. -/
theorem literalClosedSource_bValues_iff_RHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (e : {v : Vertex F K // v ∈ X} → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ u v : {v : Vertex F K // v ∈ X},
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (e u) (e v))
    (heLevel : ∀ u v : {v : Vertex F K // v ∈ X},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v))
    (heOrder : ∀ v u w : {v : Vertex F K // v ∈ X},
      u.val ∈ birthBlockOf F K v.val →
      w.val ∈ birthBlockOf F K v.val →
      birthOrdinal F K u.val < birthOrdinal F K w.val →
      birthOrdinal F K (e u) < birthOrdinal F K (e w)) :
    let f := extendClosedSourceMap F K X e
    (∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v)) ↔
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        (∀ r ∈ s, IsBirthRoot F K r) →
        (birthDClosedHull F K s).image f =
          birthDClosedHull F K (s.image f)) ∧
      (∀ s : Finset (Vertex F K),
        (∀ v ∈ s, v ∈ X) →
        ((∀ r ∈ s, IsBirthRoot F K r) ↔
          (∀ r ∈ s.image f, IsBirthRoot F K r))) := by
  let f := extendClosedSourceMap F K X e
  have hOn : ∀ v : Vertex F K, (hv : v ∈ X) →
      f v = e ⟨v, hv⟩ := by
    intro v hv
    exact extendClosedSourceMap_apply F K X e v hv
  have hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v := by
    intro u hu v hv huv
    rw [hOn u hu, hOn v hv] at huv
    exact congrArg Subtype.val (heInj huv)
  have hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heAdj (⟨u, hu⟩ : {w : Vertex F K // w ∈ X})
        (⟨v, hv⟩ : {w : Vertex F K // w ∈ X}))
  have hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v) := by
    intro u hu v hv
    simpa only [hOn u hu, hOn v hv] using
      (heLevel (⟨u, hu⟩ : {w : Vertex F K // w ∈ X})
        (⟨v, hv⟩ : {w : Vertex F K // w ∈ X}))
  have hOrder : PreservesBirthBlockOrderOn F K X f := by
    intro v hv u w huB hwB hlt
    have hCsubX : ∀ z ∈ birthCValue F K v, z ∈ X :=
      generatedClosure_subset_closedSet F K X hX
        ({v} : Finset (Vertex F K)) (by
          intro z hz
          have hzv : z = v := by simpa using hz
          subst z
          exact hv)
    have hu : u ∈ X :=
      hCsubX u ((birthBlockOf_mem_iff F K v u).mp huB).1
    have hw : w ∈ X :=
      hCsubX w ((birthBlockOf_mem_iff F K v w).mp hwB).1
    have hLocal := heOrder
      (⟨v, hv⟩ : {z : Vertex F K // z ∈ X})
      (⟨u, hu⟩ : {z : Vertex F K // z ∈ X})
      (⟨w, hw⟩ : {z : Vertex F K // z ∈ X})
      huB hwB hlt
    simpa only [hOn u hu, hOn w hw] using hLocal
  exact bValues_iff_RHValues_on_closedSet F K X hX f
    hf hAdj hLevel hOrder

end CFCoherentTower
end BigHrushovski
