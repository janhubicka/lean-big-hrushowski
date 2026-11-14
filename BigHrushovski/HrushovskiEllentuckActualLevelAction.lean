import BigHrushovski.HrushovskiEllentuckActualCountableRH
import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness

/-!
# Recovering birth-level actions from ordered C_F embeddings

The birth-level preorder is part of the published ordered
functional expansion. An embedding preserving and reflecting
this preorder acts on its equivalence classes.

When every stage has an empty-support request, every level
contains an actual vertex. Choosing one such vertex at each
level therefore recovers a strictly increasing level map.
The result is independent of the chosen representative because
the preorder is preserved and reflected.

This does not assume a level action as additional embedding
data. The complete R(v), partial H(S), and canonical order
conditions are kept exactly as in the previous countable
lifting theorem. No claim is made for a reduct which does
not name the birth-level preorder.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- One actual vertex on each birth level, supplied by an
empty-support request. The corresponding complete support is
also a singleton, but that stronger fact is not needed here. -/
noncomputable def birthLevelRepresentative
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (n : ℕ) : Vertex F K :=
  birthRoot F K n (Classical.choose (hReq n))

@[simp] theorem birthLevelRepresentative_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (n : ℕ) :
    (birthLevelRepresentative F K hReq n).1 = n := rfl

/-- A global embedding of the named ordered (R,H) structure
without first specifying the induced map on birth levels. -/
def IsGlobalOrderedRHEmbeddingWithoutAction
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K) : Prop :=
  Function.Injective f ∧
  (∀ u v : Vertex F K,
    (countableGraph F K).adj u v ↔
      (countableGraph F K).adj (f u) (f v)) ∧
  (∀ u v : Vertex F K,
    BirthLevelLe F K u v ↔
      BirthLevelLe F K (f u) (f v)) ∧
  (∀ u v : Vertex F K,
    canonicalBirthLt F K u v ↔
      canonicalBirthLt F K (f u) (f v)) ∧
  GlobalRHValues F K f

/-- Read the image level at the chosen representative of n. -/
noncomputable def inducedBirthLevelAction
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K) : ℕ → ℕ :=
  fun n => (f (birthLevelRepresentative F K hReq n)).1

/-- The induced map is constant on every source level.
Preservation and reflection of the preorder, rather than
injectivity of f, give this conclusion. -/
theorem inducedBirthLevelAction_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (hPre : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔
        BirthLevelLe F K (f u) (f v))
    (v : Vertex F K) :
    (f v).1 = inducedBirthLevelAction F K hReq f v.1 := by
  let z := birthLevelRepresentative F K hReq v.1
  have hz : z.1 = v.1 := by
    simp [z]
  have h1 : BirthLevelLe F K v z := by
    change v.1 ≤ z.1
    exact hz.ge
  have h2 : BirthLevelLe F K z v := by
    change z.1 ≤ v.1
    exact hz.le
  have hf1 : (f v).1 ≤ (f z).1 := (hPre v z).mp h1
  have hf2 : (f z).1 ≤ (f v).1 := (hPre z v).mp h2
  exact Nat.le_antisymm hf1 hf2

/-- Reflected comparison makes the induced level map strictly
increasing. This uses actual representatives at both levels. -/
theorem inducedBirthLevelAction_strictMono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (hPre : ∀ u v : Vertex F K,
      BirthLevelLe F K u v ↔
        BirthLevelLe F K (f u) (f v)) :
    StrictMono (inducedBirthLevelAction F K hReq f) := by
  intro n m hnm
  let u := birthLevelRepresentative F K hReq n
  let v := birthLevelRepresentative F K hReq m
  have hu : u.1 = n := by simp [u]
  have hv : v.1 = m := by simp [v]
  have hBefore : BirthLevelLe F K u v := by
    change u.1 ≤ v.1
    omega
  have hImageLe : (f u).1 ≤ (f v).1 :=
    (hPre u v).mp hBefore
  have hImageLt : (f u).1 < (f v).1 := by
    by_contra hnot
    have hReverse : BirthLevelLe F K (f v) (f u) := by
      change (f v).1 ≤ (f u).1
      omega
    have hSourceReverse : BirthLevelLe F K v u :=
      (hPre v u).mpr hReverse
    change v.1 ≤ u.1 at hSourceReverse
    omega
  exact hImageLt

/-- Once a global level action has been specified, it is forced
by the action on the actual vertices of each birth level. -/
theorem inducedBirthLevelAction_unique
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K) (h : ℕ → ℕ)
    (hBirth : ∀ v : Vertex F K, (f v).1 = h v.1) :
    inducedBirthLevelAction F K hReq f = h := by
  funext n
  change (f (birthLevelRepresentative F K hReq n)).1 = h n
  rw [hBirth (birthLevelRepresentative F K hReq n),
      birthLevelRepresentative_birth F K hReq n]

/-- Every embedding of the named ordered (R,H) language
has a canonical strictly increasing birth-level action,
provided each level is represented. -/
theorem orderedRHEmbedding_has_strict_level_action
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedRHEmbeddingWithoutAction F K f) :
    ∃ h : ℕ → ℕ, StrictMono h ∧
      IsGlobalOrderedRHEmbedding F K h f := by
  obtain ⟨hfInj, hfAdj, hfPre, hfOrder, hfRH⟩ := hf
  let h := inducedBirthLevelAction F K hReq f
  exact ⟨h, inducedBirthLevelAction_strictMono
    F K hReq f hfPre, hfInj, hfAdj, hfPre, hfOrder,
    (fun v => inducedBirthLevelAction_exact
      F K hReq f hfPre v), hfRH⟩

/-- The specified birth-level action is automatic and unique
for every ordered (R,H) embedding of the published expansion. -/
theorem orderedRHEmbedding_iff_exists_strict_level_action
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K) :
    IsGlobalOrderedRHEmbeddingWithoutAction F K f ↔
      ∃ h : ℕ → ℕ, StrictMono h ∧
        IsGlobalOrderedRHEmbedding F K h f := by
  constructor
  · exact orderedRHEmbedding_has_strict_level_action F K hReq f
  · rintro ⟨h, hh, hf⟩
    exact ⟨hf.1, hf.2.1, hf.2.2.1,
      hf.2.2.2.1, hf.2.2.2.2.2⟩

end BigHrushovski.CFCoherentTower
