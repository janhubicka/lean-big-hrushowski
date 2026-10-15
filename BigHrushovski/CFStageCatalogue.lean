import BigHrushovski.CFOrderedCatalogue
import BigHrushovski.CFSupportPersistence

/-!
# The finite catalogue of one-block requests at a C_F level

An old finite graph U has only finitely many actual vertex subsets P.
For each P that is strictly d-closed in U, the bounded ordered-local
catalogue provides finitely many complete graph codes over the
*literally named* support P.

A StageRequest is precisely such a pair: an actual d-closed support
and one bounded ordered local code, with the support carried by
the subtype of U.  Thus distinct actual supports are not identified
even if their induced subgraphs are abstractly isomorphic.

The caller supplies a separate size bound K(P) and admissibility
predicate Allowed(P,n,G) for each support. These inputs must eventually
be instantiated by the published growth-function class C_F.
No class-level free amalgamation or countable genericity is claimed.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The literal vertex set of a finite old support, retaining its
inclusion into the ambient graph rather than choosing a new numbering. -/
abbrev SupportCarrier (U : Type*) (P : Finset U) :=
  {u : U // u ∈ P}

/-- The graph induced by a finite support in the old stage. -/
noncomputable def supportGraph (G : GraphOn U) (P : Finset U) :
    GraphOn (SupportCarrier U P) :=
  G.pullback Subtype.val

/-- An externally specified predicate for permitted local graph codes,
indexed by the *actual* support P. -/
abbrev AllowedLocal (U : Type*) :=
  (P : Finset U) → (n : ℕ) →
    GraphOn (Sum (SupportCarrier U P) (Fin n)) → Prop

/-- One one-block request to be scheduled at the present finite level.

A support is a literal d-closed vertex subset P of the old graph;
the code is a bounded ordered local type whose base is exactly the
induced graph on P, with inherited vertex names. -/
structure StageRequest
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) where
  support : Finset U
  supportClosed : G.toPredimension.IsDClosed support Finset.univ
  code : CFLocalCatalogue.BoundedOrderedLocalType
    (SupportCarrier U support)
    (supportGraph G support)
    (Allowed support) (bound support)

/-- All level requests form a finite type: finitely many actual
supports, each with a finite bounded ordered-local catalogue. -/
noncomputable instance finite_stageRequest
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Finite (StageRequest G Allowed bound) := by
  classical
  let family : (P : Finset U) → Type _ := fun P =>
    CFLocalCatalogue.BoundedOrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (Allowed P) (bound P)
  letI : ∀ P : Finset U, Finite (family P) := fun P => by
    dsimp [family]
    infer_instance
  have hInjective : Function.Injective
      (fun r : StageRequest G Allowed bound =>
        (⟨r.support, r.code⟩ : Σ P : Finset U, family P)) := by
    intro a b hab
    cases a with
    | mk aP ha aCode =>
      cases b with
      | mk bP hb bCode =>
        cases hab
        rfl
  exact Finite.of_injective
    (fun r : StageRequest G Allowed bound =>
      (⟨r.support, r.code⟩ : Σ P : Finset U, family P)) hInjective

/-- The full finite list of requests over all actual d-closed supports.
A record occurs once as an element of this finite set. -/
noncomputable def stageCatalogue
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Finset (StageRequest G Allowed bound) := by
  classical
  letI : Fintype (StageRequest G Allowed bound) := Fintype.ofFinite _
  exact Finset.univ

theorem mem_stageCatalogue
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    r ∈ stageCatalogue G Allowed bound := by
  classical
  simp [stageCatalogue]

/-- A prescribed finite ordered local code appears over its exact
d-closed old support whenever its size lies within the supplied bound.
The code itself, not merely its abstract isomorphism type, is retained. -/
theorem includes_ordered_code
    (G : GraphOn U)
    (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (P : Finset U)
    (hP : G.toPredimension.IsDClosed P Finset.univ)
    (n : ℕ) (hn : n ≤ bound P)
    (t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (Allowed P) n) :
    (⟨P, hP,
      CFLocalCatalogue.toBounded
        (supportGraph G P) (Allowed P) (bound P) n hn t⟩ :
      StageRequest G Allowed bound) ∈
        stageCatalogue G Allowed bound := by
  exact mem_stageCatalogue G Allowed bound _

/-- Every scheduled support is literally d-closed in the finite
old graph; no membership in an unrelated ambient graph is implied. -/
theorem StageRequest.support_dClosed
    {G : GraphOn U}
    {Allowed : AllowedLocal U}
    {bound : Finset U → ℕ}
    (r : StageRequest G Allowed bound) :
    G.toPredimension.IsDClosed r.support Finset.univ :=
  r.supportClosed

end CFStageCatalogue
end BigHrushovski
