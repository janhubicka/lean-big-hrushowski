import BigHrushovski.RamseyTransfer

/-!
# Finite Ramsey transfer for a level-coded class

This is the last combinatorial step of the paper's finite Ramsey proof
for the functional C_F class. The ordinary finite Ramsey arrow and the
existence of unique concrete level codes are explicit hypotheses.

The proof is deliberately independent of the d-closed or strong
extension calculus. It does not assert that finite unions of C_F
substructures are closed, nor that every prescribed level assignment
has a unique lift: those remain concrete dependencies.
-/

namespace BigHrushovski
namespace RamseyTransfer

/-- The familiar finite arrow N -> (b)^a_r, with increasing tuples
as the finite subsets. The colour of every a-tuple inside the chosen
b-tuple is the same. -/
def FiniteCoordinateArrow (a b N r : ℕ) : Prop :=
  ∀ colour : (Fin a ↪o Fin N) → Fin r,
    ∃ q : Fin b ↪o Fin N,
      ∀ f g : Fin a ↪o Fin b,
        colour (f.trans q) = colour (g.trans q)

/-- A finite coordinate arrow gives the desired arrow between two
concrete objects when each embedding into the host has a unique level
tuple and composition reflects the level tuples.

The map of embeddings A into B to a-tuples of b need not be onto:
Ramsey homogeneity of all coordinate a-tuples is stronger than
homogeneity of only those which are realized inside B. -/
theorem finiteRamsey_of_levelCodes
    {EmbAQ EmbBQ EmbAB : Type*}
    (a b N r : ℕ)
    (arrow : FiniteCoordinateArrow a b N r)
    (codeA : EmbAQ ≃ (Fin a ↪o Fin N))
    (codeB : EmbBQ ≃ (Fin b ↪o Fin N))
    (codeAB : EmbAB → (Fin a ↪o Fin b))
    (post : EmbBQ → EmbAB → EmbAQ)
    (hcompat : ∀ (q : EmbBQ) (f : EmbAB),
      codeA (post q f) = (codeAB f).trans (codeB q)) :
    ∀ colour : EmbAQ → Fin r,
      ∃ q : EmbBQ, ∀ f g : EmbAB,
        colour (post q f) = colour (post q g) := by
  intro colour
  obtain ⟨q, hmono⟩ := arrow (fun u => colour (codeA.symm u))
  refine ⟨codeB.symm q, ?_⟩
  have hcode (f : EmbAB) :
      colour (post (codeB.symm q) f) =
        colour (codeA.symm ((codeAB f).trans q)) := by
    congr 1
    apply codeA.injective
    simpa using hcompat (codeB.symm q) f
  intro f g
  calc
    colour (post (codeB.symm q) f) =
        colour (codeA.symm ((codeAB f).trans q)) := hcode f
    _ = colour (codeA.symm ((codeAB g).trans q)) :=
      hmono (codeAB f) (codeAB g)
    _ = colour (post (codeB.symm q) g) := (hcode g).symm

end RamseyTransfer
end BigHrushovski
