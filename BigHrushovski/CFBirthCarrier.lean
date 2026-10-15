import BigHrushovski.CFCoherentStages

/-!
# A countable, birth-labelled carrier for the C_F tower

The successive finite stages have genuinely different carrier types:
U_(n+1) = U_n + (request tag, fresh ordinal).

A vertex is determined by the unique level at which it was first
introduced and by its tag in that level. Thus the countable carrier
can be defined directly as a dependent sum of fresh vertex types.
No quotient by an eventual-equality relation is needed.

The canonical map from every finite stage into this birth carrier
is compatible with old-stage injections, injective, and its image
consists of vertices born strictly before that stage index.
Every birth vertex occurs at the immediately succeeding finite
stage.

This module constructs the carrier and stage maps only. The induced
graph on the countable carrier, strict global d-closedness, and
genericity are separate subsequent obligations.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The fresh request-tagged vertices introduced between U_n and
U_(n+1), retaining their actual dependent request records. -/
abbrev FreshAt (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :=
  FreshCarrier (stage F K n).graph
    (GrowthAllowedLocal F)
    (fun P => K P.card)

/-- Every fresh layer is finite because its set of complete
ordered local requests is finite. -/
noncomputable instance freshAt_finite (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) : Finite (FreshAt F K n) := by
  classical
  letI : Fintype (FreshAt F K n) := by
    unfold FreshAt
    infer_instance
  infer_instance

/-- The canonical countable universe: a vertex remembers its
birth level and exact fresh request tag. -/
abbrev Vertex (F : ℕ → ℝ) (K : ℕ → ℕ) :=
  Σ n : ℕ, FreshAt F K n

noncomputable instance vertex_countable (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Countable (Vertex F K) := by
  classical
  infer_instance

/-- Every old vertex keeps its birth identity on passage to the
next stage. New vertices get the current level as their birth
index. These cases use the actual dependent Sum carrier of each
successor stage, not an arbitrary isomorphism. -/
noncomputable def toVertex (F : ℕ → ℝ) (K : ℕ → ℕ) :
    (n : ℕ) → (stage F K n).carrier → Vertex F K
  | 0, v => Fin.elim0 v
  | n + 1, Sum.inl v => toVertex F K n v
  | n + 1, Sum.inr v => ⟨n, v⟩

/-- The canonical map is compatible with the literal
Sum.inl inclusion of an old stage into its successor. -/
theorem toVertex_old (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (v : (stage F K n).carrier) :
    toVertex F K (n + 1) (Sum.inl v) = toVertex F K n v :=
  rfl

/-- Each genuinely new tagged vertex receives exactly the
birth level at which it is added. -/
theorem toVertex_new (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (v : FreshAt F K n) :
    toVertex F K (n + 1) (Sum.inr v) =
      (⟨n, v⟩ : Vertex F K) :=
  rfl

/-- A vertex in the nth finite stage was born before stage n.
This rules out an accidental identification between a fresh
vertex and any vertex from the old stage. -/
theorem toVertex_birth_lt (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (v : (stage F K n).carrier) :
    (toVertex F K n v).1 < n := by
  induction n generalizing v with
  | zero =>
      exact Fin.elim0 v
  | succ n ih =>
      cases v with
      | inl old =>
          exact (ih old).trans (Nat.lt_succ_self n)
      | inr new =>
          exact Nat.lt_succ_self n

/-- Finite stages embed injectively into the birth-labelled
carrier; no old vertex is identified with a new one, and
distinct fresh tags remain distinct. -/
theorem toVertex_injective (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) : Function.Injective (toVertex F K n) := by
  induction n with
  | zero =>
      intro a b _
      exact Fin.elim0 a
  | succ n ih =>
      intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b =>
              exact congrArg Sum.inl (ih hab)
          | inr b =>
              have hIndex :
                  (toVertex F K n a).1 = n :=
                congrArg Sigma.fst hab
              exact False.elim ((Nat.ne_of_lt
                (toVertex_birth_lt F K n a)) hIndex)
      | inr a =>
          cases b with
          | inl b =>
              have hIndex :
                  (toVertex F K n b).1 = n :=
                (congrArg Sigma.fst hab).symm
              exact False.elim ((Nat.ne_of_lt
                (toVertex_birth_lt F K n b)) hIndex)
          | inr b =>
              have hab' : (⟨n, a⟩ : Vertex F K) = ⟨n, b⟩ := hab
              cases hab'
              rfl

/-- Every vertex of the countable carrier is represented in a
finite stage, namely immediately after its birth level. -/
theorem everyVertex_in_stage (F : ℕ → ℝ) (K : ℕ → ℕ)
    (v : Vertex F K) :
    ∃ n : ℕ, ∃ x : (stage F K n).carrier,
      toVertex F K n x = v := by
  rcases v with ⟨n, fresh⟩
  exact ⟨n + 1, Sum.inr fresh, rfl⟩

end CFCoherentTower
end BigHrushovski
