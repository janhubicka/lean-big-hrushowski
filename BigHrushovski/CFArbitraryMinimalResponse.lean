import BigHrushovski.CFCanonicalNamedSupport
import BigHrushovski.CFLocalSplitCertificates
import BigHrushovski.CFLocalFreshBound
import BigHrushovski.CFNamedOneStepResponse

/-!
# Respond to any finite minimal strict C_F extension over a fixed old stage

This theorem removes all intermediate local-coding assumptions from
the already certified namedLocalExtension_globalResponse theorem.

Start with a complete finite graph H on an old carrier S and new
carrier B. Assume that the entire old part is a minimal strict
d-closed substructure of H and H belongs to the exact C_F growth
class. An injective induced map f:S→U_n is prescribed and has a
d-closed image in the actual tagged finite stage U_n.

The canonical finite support theorem determines a literal old set
P⊆S, gives its d-closedness in S, the no-neighbours-outside-P
property, and minimal/exact support certificates for the local
interval P⊕B. The complete split graph transport carries its
growth, minimality and exact support properties to the required
subtype graph on P⊕B. The finite growth-size lemma, under an
explicit numerical inverse property of F and K, bounds |B| by
K(|f[P]|). Thus every hypothesis of the named one-step response
is obtained from the original minimal extension.

The conclusion constructs an induced embedding of the entire
ordered extension S⊕Fin(|B|) into the actual countable birth graph,
fixes the prescribed old source pointwise and has globally strictly
d-closed image. There is no genericity assumption or abstract
existence of a desired extension in the target.

The remaining countable Fraïssé theorem will combine this
minimal-step response with the certified finite minimal-step
decomposition and the real growth-to-integer inverse theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFLocalCatalogue

variable {S B : Type*} [Fintype S] [DecidableEq S]
variable [Fintype B] [DecidableEq B] [LinearOrder B]

/-- A finite proper minimal strict d-closed extension of the
entire old part by B has a nonempty fresh block. -/
theorem fresh_nonempty_of_minimal
    (H : GraphOn (Sum S B))
    (hMin : H.toPredimension.IsMinimalDClosedStep
      (actualOld S B) Finset.univ) :
    (Finset.univ : Finset B).Nonempty := by
  classical
  by_contra hn
  have hFreshEmpty : actualFresh S B = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨b, _, _⟩ := Finset.mem_image.mp hx
    exact hn ⟨b, Finset.mem_univ b⟩
  have hUnion :
      actualOld S B ∪ actualFresh S B =
        (Finset.univ : Finset (Sum S B)) := by
    ext x
    cases x with
    | inl s => simp [actualOld, actualFresh]
    | inr b => simp [actualOld, actualFresh]
  have hOldFull :
      actualOld S B = (Finset.univ : Finset (Sum S B)) := by
    simpa only [hFreshEmpty, Finset.union_empty] using hUnion
  exact hMin.2.1 hOldFull

/-- Every minimal strict C_F extension of a prescribed finite
old stage is realized in the countable tagged construction,
without supplying an already normalized local request.

The conclusion is a complete induced graph embedding with
global strict d-closedness. The only remaining external
assumption is the explicit numerical inverse domination
property needed to select K. -/
theorem arbitraryMinimalCF_globalResponse
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k m : ℕ,
      F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k)
    (n : ℕ)
    (H : GraphOn (Sum S B))
    (hMinimal : H.toPredimension.IsMinimalDClosedStep
      (actualOld S B) Finset.univ)
    (hGrowth : H.IsGrowthSparse F Finset.univ)
    (f : S → (stage F K n).carrier)
    (hf : Function.Injective f)
    (hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage F K n).graph.adj (f x) (f y))
    (hSourceClosed : (stage F K n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ) :
    ∃ g : Sum S (Fin (Fintype.card B)) → Vertex F K,
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) = toVertex F K n (f x)) ∧
      (∀ x y : Sum S (Fin (Fintype.card B)),
        (H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (increasingNewBlock (B := B)).toEquiv)).adj x y ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin (Fintype.card B)))).image g) := by
  classical
  let P := canonicalNamedSupport H
  obtain ⟨hP, hBack, hLocalMin, hExact⟩ :=
    canonicalNamedSupport_certificates H hMinimal
  obtain ⟨hLocalGrowth, hLocalMinimal, hLocalSupport⟩ :=
    oldSubsetLocal_certificates H F P hGrowth hLocalMin hExact
  obtain ⟨b, _⟩ := fresh_nonempty_of_minimal H hMinimal
  have hSize : Fintype.card B ≤ K (P.image f).card :=
    minimalLocal_fresh_size_le F K hInverse H P
      hLocalMin hGrowth b f hf
  exact namedLocalExtension_globalResponse F K n H f hf
    hOld hSourceClosed P hP
    hLocalGrowth hLocalMinimal hLocalSupport hBack hSize

end CFCoherentTower
end BigHrushovski
