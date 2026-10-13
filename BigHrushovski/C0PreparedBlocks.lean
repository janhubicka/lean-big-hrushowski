import BigHrushovski.C0LocalFreeConverse
import BigHrushovski.C0FiniteRuns

/-!
# Finite sequences of prepared C0 closure-components

The local C0 lemma proves that a minimal strong step P < P ∪ B
remains minimal after attaching a larger old set A, provided
P ⊆ A, A is disjoint from the fresh block B, and there are no
edges from B to A \ P.

A prepared list records these hypotheses *at every stage*.  This
module proves that the resulting concatenation consists entirely
of minimal strong steps.  It makes no assumption that A is itself
globally strong, and it does not assert preservation of the unary
closure values in a functional free amalgam.

The latter is a separate obligation in Proposition C0-free-generic.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- A finite list of local minimal blocks (P,B), prepared for attachment
to the successive old prefixes. The no-cross condition must hold for
the *current* prefix, not merely for the original common base. -/
def IsPreparedBlockSequence (G : GraphOn V) (a : Finset V) :
    List (Finset V × Finset V) → Prop
  | [] => True
  | block :: rest =>
      block.1 ⊆ a ∧
      Disjoint a block.2 ∧
      G.NoCrossEdges a (block.1 ∪ block.2) ∧
      G.toPredimension.IsMinimalStrongStep
        block.1 (block.1 ∪ block.2) ∧
      G.IsPreparedBlockSequence (a ∪ block.2) rest

/-- The terminal old set obtained by adjoining all the fresh blocks. -/
def attachedBlocks (a : Finset V)
    (blocks : List (Finset V × Finset V)) : Finset V :=
  blocks.foldl (fun old block => old ∪ block.2) a

/-- Attaching a prepared finite sequence yields a chain of minimal
strong extensions, including every boundary between two blocks. -/
theorem preparedBlocks_minimalStrongChain
    (blocks : List (Finset V × Finset V)) :
    ∀ a : Finset V, G.IsPreparedBlockSequence a blocks →
      Predimension.MinimalStrongChain
        G.toPredimension a (attachedBlocks a blocks) := by
  induction blocks with
  | nil =>
      intro a _
      exact Predimension.MinimalStrongChain.refl a
  | cons block rest ih =>
      intro a h
      change block.1 ⊆ a ∧
        Disjoint a block.2 ∧
        G.NoCrossEdges a (block.1 ∪ block.2) ∧
        G.toPredimension.IsMinimalStrongStep
          block.1 (block.1 ∪ block.2) ∧
        G.IsPreparedBlockSequence (a ∪ block.2) rest at h
      rcases h with ⟨hLower, hFresh, hNoCross, hMinimal, hRest⟩
      change Predimension.MinimalStrongChain G.toPredimension
        a (attachedBlocks (a ∪ block.2) rest)
      exact Predimension.MinimalStrongChain.step
        (G.minimalStrongStep_enlarged_of_local
          block.1 a block.2 hLower hFresh hNoCross hMinimal)
        (ih (a ∪ block.2) hRest)

/-- The endpoints of every prepared sequence form a strong extension. -/
theorem preparedBlocks_strong
    (a : Finset V) (blocks : List (Finset V × Finset V))
    (h : G.IsPreparedBlockSequence a blocks) :
    G.toPredimension.IsStrong a (attachedBlocks a blocks) :=
  (G.preparedBlocks_minimalStrongChain blocks a h).isStrong

end GraphOn
end BigHrushovski
