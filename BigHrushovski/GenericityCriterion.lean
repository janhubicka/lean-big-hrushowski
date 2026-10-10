import BigHrushovski.FiniteCatalogue
import BigHrushovski.StrongChain

/-!
# Fair strong extension requests and the genericity criterion

A potential request is a labelled finite strong extension A ≤ B and
a map of A into the natural-number carrier. The request applies at a
finite stage when its base map is an induced strong embedding there.
It is answered when the target B embeds strongly into the next stage
over the prescribed base.

If a covering strong chain answers every applicable scheduled request,
the repeated fair enumeration implies the strong extension property
in its union. The proof uses global strongness of chain stages.

This is a conditional criterion, not a construction of a chain
satisfying its local response hypothesis.
-/

namespace BigHrushovski
namespace FiniteCatalogue

variable (G : GraphOn ℕ)

/-- A request's source map is induced and strong inside a finite stage. -/
def AppliesAt (U : Finset ℕ) (req : ExtensionRequestCatalogue) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  Function.Injective f ∧
    (∀ x y : Fin req.1,
      diagram.source.adj x y ↔ G.adj (f x) (f y)) ∧
    G.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin req.1)).image f) U

/-- A request's source map is a globally strong induced embedding. -/
def AppliesGlobally (req : ExtensionRequestCatalogue) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  Function.Injective f ∧
    (∀ x y : Fin req.1,
      diagram.source.adj x y ↔ G.adj (f x) (f y)) ∧
    G.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset (Fin req.1)).image f)

/-- The finite target is embedded strongly into the specified stage,
with its base embedding equal to the prescribed source map. -/
def RespondsAt (U : Finset ℕ) (req : ExtensionRequestCatalogue) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  ∃ g : Fin req.2.1 → ℕ,
    Function.Injective g ∧
    (∀ x y : Fin req.2.1,
      diagram.target.adj x y ↔ G.adj (g x) (g y)) ∧
    (∀ x : Fin req.1, g (diagram.embedding x) = f x) ∧
    G.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin req.2.1)).image g) U

/-- The strong extension is realized in the entire ambient graph. -/
def RespondsGlobally (req : ExtensionRequestCatalogue) : Prop :=
  let diagram := req.2.2.1
  let f := req.2.2.2
  ∃ g : Fin req.2.1 → ℕ,
    Function.Injective g ∧
    (∀ x y : Fin req.2.1,
      diagram.target.adj x y ↔ G.adj (g x) (g y)) ∧
    (∀ x : Fin req.1, g (diagram.embedding x) = f x) ∧
    G.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset (Fin req.2.1)).image g)

/-- Every applicable finite labelled strong extension is realized
over its existing strong image in the ambient graph. -/
def HasStrongExtensionProperty : Prop :=
  ∀ req : ExtensionRequestCatalogue,
    G.AppliesGlobally req → G.RespondsGlobally req

/-- A fair construction that locally responds to scheduled strong
requests has the full strong extension property in its union.

The local response condition remains an explicit hypothesis. -/
theorem strongExtensionProperty_of_fairResponses
    (chain : Predimension.StrongChain G.toPredimension)
    (hRespond : ∀ stage : ℕ, ∀ req : ExtensionRequestCatalogue,
      fairRequest stage = some req →
      G.AppliesAt (chain.stage stage) req →
      G.RespondsAt (chain.stage (stage + 1)) req) :
    G.HasStrongExtensionProperty := by
  intro req hGlob
  let S : Finset ℕ :=
    (Finset.univ : Finset (Fin req.1)).image req.2.2.2
  obtain ⟨n, hn⟩ := chain.contains_finite S
  obtain ⟨k, hnk, hk⟩ := fairRequest_after req n
  have hSstage : S ⊆ chain.stage k :=
    hn.trans (chain.stage_monotone hnk)
  have hApplicable : G.AppliesAt (chain.stage k) req := by
    obtain ⟨hfInj, hfInd, hfGlobal⟩ := hGlob
    exact ⟨hfInj, hfInd, hfGlobal (chain.stage k) hSstage⟩
  obtain ⟨g, hgInj, hgInd, hgBase, hgStrong⟩ :=
    hRespond k req hk hApplicable
  refine ⟨g, hgInj, hgInd, hgBase, ?_⟩
  exact G.toPredimension.globallyStrong_of_strong_in_global
    hgStrong (chain.stage_global (k + 1))

end FiniteCatalogue
end BigHrushovski
