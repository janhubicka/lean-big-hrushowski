import BigHrushovski.CFDClosedChain
import BigHrushovski.CFGrowthClass
import BigHrushovski.FiniteCatalogue
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing

/-!
# A fair-response criterion for countable d-closed C_F generics

All finite growth-class graphs and finite d-closed embedding
diagrams admit a countable labelled catalogue. A potential
request consists of such a diagram and a map from its source
into the natural-number ambient carrier.

If a covering chain of finite strictly d-closed graph stages
answers every locally applicable request when it appears in
the repeated fair enumeration, then the countable ambient
graph has the d-closed extension property.

This is a conditional genericity criterion, not a construction
of the level sequence or a claim that the tagged stages have
already been represented coherently on the natural numbers.
Its purpose is to isolate that remaining construction task.
-/

namespace BigHrushovski
namespace CFDClosedGenericity

/-- A finite induced d-closed extension diagram in the
real-valued growth-function class. -/
structure DClosedDiagram (F : ℕ → ℝ) (n m : ℕ) where
  source : GraphOn (Fin n)
  target : GraphOn (Fin m)
  embedding : Fin n → Fin m
  inj : Function.Injective embedding
  induced : ∀ x y : Fin n,
    source.adj x y ↔ target.adj (embedding x) (embedding y)
  growthSource : source.IsGrowthSparse F Finset.univ
  growthTarget : target.IsGrowthSparse F Finset.univ
  dclosed : target.toPredimension.IsDClosed
    ((Finset.univ : Finset (Fin n)).image embedding)
    Finset.univ

/-- At fixed finite sizes, the graph and embedding determine
the entire proof-valued diagram uniquely. -/
noncomputable instance finite_dClosedDiagram
    (F : ℕ → ℝ) (n m : ℕ) :
    Finite (DClosedDiagram F n m) := by
  classical
  have h : Function.Injective
      (fun d : DClosedDiagram F n m =>
        (d.source, d.target, d.embedding)) := by
    intro d e heq
    cases d
    cases e
    cases heq
    rfl
  exact Finite.of_injective
    (fun d : DClosedDiagram F n m =>
      (d.source, d.target, d.embedding)) h

/-- All finite labelled d-closed extension diagrams. -/
abbrev DClosedDiagramCatalogue (F : ℕ → ℝ) :=
  Σ n : ℕ, Σ m : ℕ, DClosedDiagram F n m

noncomputable instance countable_diagrams (F : ℕ → ℝ) :
    Countable (DClosedDiagramCatalogue F) := by
  infer_instance

/-- A diagram with a proposed actual source embedding into ℕ. -/
abbrev DClosedRequestCatalogue (F : ℕ → ℝ) :=
  Σ n : ℕ, Σ m : ℕ, DClosedDiagram F n m × (Fin n → ℕ)

noncomputable instance countable_requests (F : ℕ → ℝ) :
    Countable (DClosedRequestCatalogue F) := by
  infer_instance

noncomputable instance encodable_requests (F : ℕ → ℝ) :
    Encodable (DClosedRequestCatalogue F) :=
  Encodable.ofCountable (DClosedRequestCatalogue F)

/-- Visit every labelled d-closed extension request infinitely often,
with a separate repetition counter in the second pairing component. -/
noncomputable def fairDClosedRequest (F : ℕ → ℝ) (stage : ℕ) :
    Option (DClosedRequestCatalogue F) :=
  (Encodable.decode : ℕ → Option (DClosedRequestCatalogue F))
    (Nat.unpair stage).1

/-- Every finite request reappears beyond any prescribed stage. -/
theorem fairDClosedRequest_after (F : ℕ → ℝ)
    (req : DClosedRequestCatalogue F) (threshold : ℕ) :
    ∃ stage : ℕ, threshold ≤ stage ∧
      fairDClosedRequest F stage = some req := by
  refine ⟨Nat.pair (Encodable.encode req) threshold,
    Nat.right_le_pair _ _, ?_⟩
  simp [fairDClosedRequest, Nat.unpair_pair, Encodable.encodek]

variable (G : GraphOn ℕ) (F : ℕ → ℝ)

/-- The labelled source is an induced, strictly d-closed
subgraph of the specified finite stage. -/
def AppliesAt (U : Finset ℕ)
    (req : DClosedRequestCatalogue F) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  Function.Injective f ∧
    (∀ x y : Fin req.1,
      diagram.source.adj x y ↔ G.adj (f x) (f y)) ∧
    G.toPredimension.IsDClosed
      ((Finset.univ : Finset (Fin req.1)).image f) U

/-- The labelled source is an induced globally d-closed
subgraph of the entire countable ambient graph. -/
def AppliesGlobally (req : DClosedRequestCatalogue F) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  Function.Injective f ∧
    (∀ x y : Fin req.1,
      diagram.source.adj x y ↔ G.adj (f x) (f y)) ∧
    G.toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset (Fin req.1)).image f)

/-- A finite-stage response strongly respects the named source:
it embeds the complete target diagram over the given source map,
with the target image strictly d-closed in the new finite stage. -/
def RespondsAt (U : Finset ℕ)
    (req : DClosedRequestCatalogue F) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  ∃ g : Fin req.2.1 → ℕ,
    Function.Injective g ∧
    (∀ x y : Fin req.2.1,
      diagram.target.adj x y ↔ G.adj (g x) (g y)) ∧
    (∀ x : Fin req.1, g (diagram.embedding x) = f x) ∧
    G.toPredimension.IsDClosed
      ((Finset.univ : Finset (Fin req.2.1)).image g) U

/-- The same response is globally strictly d-closed
in the whole ambient graph. -/
def RespondsGlobally (req : DClosedRequestCatalogue F) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  ∃ g : Fin req.2.1 → ℕ,
    Function.Injective g ∧
    (∀ x y : Fin req.2.1,
      diagram.target.adj x y ↔ G.adj (g x) (g y)) ∧
    (∀ x : Fin req.1, g (diagram.embedding x) = f x) ∧
    G.toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset (Fin req.2.1)).image g)

/-- The countable graph realizes every globally applicable
finite d-closed extension request from the C_F class. -/
def HasDClosedExtensionProperty : Prop :=
  ∀ req : DClosedRequestCatalogue F,
    AppliesGlobally G F req → RespondsGlobally G F req

/-- A covering strict d-closed chain answering every locally
applicable scheduled request has the full global d-closed
extension property. This does not require a growth-function
amalgamation theorem beyond those already encoded in the
individual diagrams and finite responses. -/
theorem dClosedExtensionProperty_of_fairResponses
    (chain : Predimension.DClosedChain G.toPredimension)
    (hRespond : ∀ stage : ℕ, ∀ req : DClosedRequestCatalogue F,
      fairDClosedRequest F stage = some req →
      AppliesAt G F (chain.stage stage) req →
      RespondsAt G F (chain.stage (stage + 1)) req) :
    HasDClosedExtensionProperty G F := by
  intro req hGlobal
  let S : Finset ℕ :=
    (Finset.univ : Finset (Fin req.1)).image req.2.2.2
  obtain ⟨n, hn⟩ := chain.contains_finite S
  obtain ⟨k, hnk, hk⟩ := fairDClosedRequest_after F req n
  have hSstage : S ⊆ chain.stage k :=
    hn.trans (chain.stage_monotone hnk)
  have hApplicable : AppliesAt G F (chain.stage k) req := by
    obtain ⟨hInj, hInd, hClosedGlobal⟩ := hGlobal
    exact ⟨hInj, hInd,
      hClosedGlobal.restrict hSstage⟩
  obtain ⟨g, hgInj, hgInd, hgBase, hgClosed⟩ :=
    hRespond k req hk hApplicable
  refine ⟨g, hgInj, hgInd, hgBase, ?_⟩
  exact G.toPredimension.globallyDClosed_of_dClosed_in_global
    hgClosed (chain.stage_global (k + 1))

end CFDClosedGenericity
end BigHrushovski
