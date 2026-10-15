import BigHrushovski.CFBatchGrowthMembership
import BigHrushovski.CFBatchRelativeDClosed

/-!
# The coherent finite tower of tagged C_F levels

The successive stages of the enumeration have different finite vertex
types. At each successor stage the old vertices are carried *literally*
by Sum.inl, while each new block has its full request tag.

Packaging a finite graph with its finite carrier permits ordinary
primitive recursion to construct the whole tower. No quotient of
a disjoint union, renaming of vertices or countable limit is needed
for this finite-stage interface.

We use the actual C_F growth predicate as the admissibility condition.
The integer-valued bound K on the size of a fresh block is explicit:
its adequacy for every minimal extension has to be established using
the published uniform d-closure bound.

The C_F free-amalgamation assumption is needed only when asserting
membership in the growth class, not for the underlying finite graphs
or their strict d-closed successor inclusions.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A finite graph together with its actual finite vertex type. The
typeclass witnesses are stored explicitly so that a tower may change
its carrier at each level. -/
structure FiniteStage where
  carrier : Type
  finiteCarrier : Fintype carrier
  decEqCarrier : DecidableEq carrier
  graph : GraphOn carrier

/-- Installed only for the carrier of a specified finite stage. -/
instance (S : FiniteStage) : Fintype S.carrier :=
  S.finiteCarrier

/-- Decidable equality is supplied by the finite stage itself. -/
noncomputable instance (S : FiniteStage) : DecidableEq S.carrier :=
  S.decEqCarrier

/-- The initial stage has no vertices. -/
noncomputable def emptyStage : FiniteStage where
  carrier := Fin 0
  finiteCarrier := inferInstance
  decEqCarrier := inferInstance
  graph := {
    adj := fun _ _ => False
    symm := by intro _ _ h; exact False.elim h
    irrefl := by intro _ h; exact False.elim h
  }

/-- Actual local requests are selected from the growth class.
A uniform cardinality bound K depends on the size of the named
old support; different supports of the same size retain their
different literal vertex names. -/
noncomputable def next (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : FiniteStage) : FiniteStage := by
  classical
  letI : Fintype S.carrier := S.finiteCarrier
  letI : DecidableEq S.carrier := S.decEqCarrier
  let allowed : AllowedLocal S.carrier := GrowthAllowedLocal F
  let bound : Finset S.carrier → ℕ := fun P => K P.card
  exact {
    carrier := LevelCarrier S.graph allowed bound
    finiteCarrier := finite_levelCarrier S.graph allowed bound
    decEqCarrier := decidableEq_levelCarrier S.graph allowed bound
    graph := levelGraph S.graph allowed bound
  }

/-- The successive finite tagged graphs, on genuinely varying
carriers. A stage is not identified with a subset of a fixed
countable graph until the direct limit is constructed. -/
noncomputable def stage (F : ℕ → ℝ) (K : ℕ → ℕ) :
    ℕ → FiniteStage
  | 0 => emptyStage
  | n + 1 => next F K (stage F K n)

/-- The old-part embedding at one actual successor level preserves
and reflects every edge, including nonedges. -/
theorem next_old_induced (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : FiniteStage) (x y : S.carrier) :
    (next F K S).graph.adj (Sum.inl x) (Sum.inl y) ↔
      S.graph.adj x y := by
  classical
  letI : Fintype S.carrier := S.finiteCarrier
  letI : DecidableEq S.carrier := S.decEqCarrier
  change
    (levelGraph S.graph (GrowthAllowedLocal F)
      (fun P => K P.card)).adj (Sum.inl x) (Sum.inl y) ↔
      S.graph.adj x y
  exact levelGraph_old_iff S.graph (GrowthAllowedLocal F)
    (fun P => K P.card) x y

/-- The complete old vertex set is strictly d-closed in the
whole next tagged graph, regardless of the growth function. -/
theorem next_old_dClosed (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : FiniteStage) :
    (next F K S).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S.carrier).image
        (Sum.inl : S.carrier → (next F K S).carrier))
      (Finset.univ : Finset (next F K S).carrier) := by
  classical
  letI : Fintype S.carrier := S.finiteCarrier
  letI : DecidableEq S.carrier := S.decEqCarrier
  change
    (levelGraph S.graph (GrowthAllowedLocal F)
      (fun P => K P.card)).toPredimension.IsDClosed
      (taggedOldDomain S.graph (GrowthAllowedLocal F)
        (fun P => K P.card)) Finset.univ
  exact levelGraph_old_dClosed_full S.graph
    (GrowthAllowedLocal F) (fun P => K P.card)

/-- Every successor embedding in the recursively defined tower
is an induced graph embedding. -/
theorem stage_succ_induced (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (x y : (stage F K n).carrier) :
    (stage F K (n + 1)).graph.adj (Sum.inl x) (Sum.inl y) ↔
      (stage F K n).graph.adj x y :=
  next_old_induced F K (stage F K n) x y

/-- The old stage is strictly d-closed in the next finite stage.
This is an unconditional theorem about the constructed finite
graphs, not yet a theorem of countable d-closed genericity. -/
theorem stage_succ_dClosed (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) :
    (stage F K (n + 1)).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset (stage F K n).carrier).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n + 1)).carrier))
      (Finset.univ : Finset (stage F K (n + 1)).carrier) :=
  next_old_dClosed F K (stage F K n)

/-- If the old graph belongs to C_F, then its actual next level
does too, under the explicit restricted d-closed free-amalgamation
hypothesis. This does not follow from monotonicity of F. -/
theorem next_growth (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : FiniteStage)
    (hOld : S.graph.IsGrowthSparse F
      (Finset.univ : Finset S.carrier))
    (hFree :
      (next F K S).graph.GrowthClosedUnderDClosedFreeJoins F) :
    (next F K S).graph.IsGrowthSparse F
      (Finset.univ : Finset (next F K S).carrier) := by
  classical
  letI : Fintype S.carrier := S.finiteCarrier
  letI : DecidableEq S.carrier := S.decEqCarrier
  change
    (levelGraph S.graph (GrowthAllowedLocal F)
      (fun P => K P.card)).IsGrowthSparse F Finset.univ
  exact levelGraph_growthSparse_of_growth_allowed S.graph
    (fun P => K P.card) F hOld hFree

/-- C_F membership of all finite stages follows by ordinary
induction from its exact base case and the class-level free-join
hypotheses at each stage. No countable limit is used. -/
theorem all_stages_growth (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hEmpty : (emptyStage.graph).IsGrowthSparse F
      (Finset.univ : Finset emptyStage.carrier))
    (hFree : ∀ n,
      (stage F K (n + 1)).graph.GrowthClosedUnderDClosedFreeJoins F) :
    ∀ n, (stage F K n).graph.IsGrowthSparse F
      (Finset.univ : Finset (stage F K n).carrier) := by
  intro n
  induction n with
  | zero =>
      exact hEmpty
  | succ n ih =>
      exact next_growth F K (stage F K n) ih (hFree n)

end CFCoherentTower
end BigHrushovski
