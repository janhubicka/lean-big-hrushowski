import BigHrushovski.C0FunctionalGrowingResponse
import BigHrushovski.C0FiniteFunctionalCatalogue

/-!
# A fair one-step successor for finite functional C₀ stages

All finite canonical stages have a genuine graph on a finite ordinal,
a minimal-strong component index, and the entire canonical
finite-valued unary operation.

The already certified finite response theorem answers any applicable
labelled functional request while increasing the stage size. If the
scheduled request is not applicable or has no decoded value, the
independent certified growth theorem supplies a larger stage.

A successor preserves every old numerical vertex label, induced
adjacency including nonedges, all complete unary values, and
self-sufficiency of the old graph. This module constructs the
one-step successor without assuming countable genericity.
The fair countable recursion and its limit remain separate.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A labelled canonical finite functional structure. Unlike a graph
stage it carries its entire one-generated finite-valued unary function
through a canonical component presentation. -/
structure FiniteFunctionalNatStage where
  size : ℕ
  blocks : ℕ
  model : FiniteFunctionalC0 size blocks

namespace FunctionalC0RequestCatalogue

/-- The actual finite functional diagram underlying a request. -/
def diagram (req : FunctionalC0RequestCatalogue) :
    FunctionalC0Diagram req.1 req.2.1 req.2.2.1 req.2.2.2.1 :=
  req.2.2.2.2.1

/-- The actual prescribed old numerical labels. -/
def labels (req : FunctionalC0RequestCatalogue) : Fin req.1 → ℕ :=
  req.2.2.2.2.2

end FunctionalC0RequestCatalogue

namespace FiniteFunctionalNatStage

/-- Applicability means that the request's source has a prescribed
complete induced *functional* embedding into the current stage.
Every complete unary value must agree, not only adjacency. -/
def Applies (s : FiniteFunctionalNatStage)
    (req : FunctionalC0RequestCatalogue) : Prop :=
  ∃ e : Fin req.1 → Fin s.size,
    Function.Injective e ∧
    (∀ x : Fin req.1, (e x).val = req.labels x) ∧
    (∀ x y : Fin req.1,
      req.diagram.source.graph.adj x y ↔
        s.model.graph.adj (e x) (e y)) ∧
    (∀ x : Fin req.1,
      s.model.unaryValue (e x) =
        (req.diagram.source.unaryValue x).image e)

/-- A finite target response embeds the entire requested target,
preserving its complete function, and is strong in the responding
finite stage. Its base agrees with the prescribed Nat labels. -/
def Responds (t : FiniteFunctionalNatStage)
    (req : FunctionalC0RequestCatalogue) : Prop :=
  ∃ g : Fin req.2.2.1 → Fin t.size,
    Function.Injective g ∧
    (∀ x y : Fin req.2.2.1,
      req.diagram.target.graph.adj x y ↔
        t.model.graph.adj (g x) (g y)) ∧
    (∀ x : Fin req.2.2.1,
      t.model.unaryValue (g x) =
        (req.diagram.target.unaryValue x).image g) ∧
    (∀ x : Fin req.1,
      (g (req.diagram.embedding x)).val = req.labels x) ∧
    t.model.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin req.2.2.1)).image g)
      Finset.univ

/-- A successor has strict growth, keeps the graph and whole unary
operation on all old numeric labels, and answers the fair request
whenever its full functional source embedding is applicable.
Old strongness is retained as a separate exact certificate. -/
structure IsFairFunctionalSuccessor
    (step : ℕ) (s t : FiniteFunctionalNatStage) where
  grows : s.size < t.size
  old : Fin s.size → Fin t.size
  old_injective : Function.Injective old
  old_labels : ∀ x : Fin s.size, (old x).val = x.val
  old_graph : ∀ x y : Fin s.size,
    s.model.graph.adj x y ↔ t.model.graph.adj (old x) (old y)
  old_values : ∀ x : Fin s.size,
    t.model.unaryValue (old x) =
      (s.model.unaryValue x).image old
  old_strong : t.model.graph.toPredimension.IsStrong
    ((Finset.univ : Finset (Fin s.size)).image old) Finset.univ
  responds : ∀ req : FunctionalC0RequestCatalogue,
    fairFunctionalC0Request step = some req →
    s.Applies req → t.Responds req

/-- In any fair scheduling step an absent or inapplicable request
still forces a genuinely fresh vertex, while preserving all old
graph and unary values and old strongness. -/
private theorem growth_fallback
    (step : ℕ) (s : FiniteFunctionalNatStage)
    (hNoRequest : ∀ req : FunctionalC0RequestCatalogue,
      fairFunctionalC0Request step = some req → ¬ s.Applies req) :
    ∃ t : FiniteFunctionalNatStage,
      IsFairFunctionalSuccessor step s t := by
  classical
  obtain ⟨m, b, M, old, hGrow, hInj, hFixed,
      hAdj, hValues, hStrong⟩ :=
    exists_growingCanonicalFunctionalC0Stage s.model
  let t : FiniteFunctionalNatStage :=
    ⟨m, b, M⟩
  refine ⟨t, ⟨hGrow, old, hInj, hFixed,
    hAdj, hValues, hStrong, ?_⟩⟩
  intro req hFair hApp
  exact (hNoRequest req hFair hApp).elim

/-- The scheduled request is realized over its **actual** old
labelled source, with strictly larger stage size. Every original
numeric vertex remains fixed and both finite copies are induced,
strong and preserve complete unary functions. -/
private theorem response_successor
    (step : ℕ) (s : FiniteFunctionalNatStage)
    (req : FunctionalC0RequestCatalogue)
    (hFair : fairFunctionalC0Request step = some req)
    (hApp : s.Applies req) :
    ∃ t : FiniteFunctionalNatStage,
      IsFairFunctionalSuccessor step s t := by
  classical
  obtain ⟨e, he, hLabels, hInd, hValues⟩ := hApp
  obtain ⟨m, b, M, old, target, hGrow,
    hOldInjective, hTargetInjective, hFixed,
    hOldAdj, hTargetAdj, hOldValue, hTargetValue,
    hOnBase, hOldStrong, hTargetStrong⟩ :=
    exists_growingFiniteOrdinalFunctionalResponse
      s.model req.diagram e he hInd hValues
  let t : FiniteFunctionalNatStage := ⟨m, b, M⟩
  refine ⟨t, ⟨hGrow, old, hOldInjective, hFixed,
    hOldAdj, hOldValue, hOldStrong, ?_⟩⟩
  intro req' hFair' _
  have hReq : req' = req :=
    Option.some.inj (hFair'.symm.trans hFair)
  subst req'
  refine ⟨target, hTargetInjective, hTargetAdj,
    hTargetValue, ?_, hTargetStrong⟩
  intro x
  calc
    (target (req.diagram.embedding x)).val =
        (old (e x)).val := congrArg Fin.val (hOnBase x).symm
    _ = (e x).val := hFixed (e x)
    _ = req.labels x := hLabels x

/-- A fair finite functional successor exists at **every** stage.
The three cases (no decoded request, inapplicable request, applicable
request) are handled without invoking a countable Fraïssé limit or
postulating that all requests are already realizable. -/
theorem exists_fairFunctionalSuccessor
    (step : ℕ) (s : FiniteFunctionalNatStage) :
    ∃ t : FiniteFunctionalNatStage,
      IsFairFunctionalSuccessor step s t := by
  classical
  cases hFair : fairFunctionalC0Request step with
  | none =>
      apply growth_fallback step s
      intro req hCode
      rw [hFair] at hCode
      cases hCode
  | some req =>
      by_cases hApp : s.Applies req
      · exact response_successor step s req hFair hApp
      · apply growth_fallback step s
        intro other hCode
        have hEq : other = req :=
          Option.some.inj (hCode.symm.trans hFair)
        subst other
        exact hApp

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
