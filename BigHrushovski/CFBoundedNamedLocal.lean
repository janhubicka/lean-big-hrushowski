import BigHrushovski.CFNamedBaseTransport
import BigHrushovski.CFGrowthNormalizedLocal

/-!
# Complete bounded C_F local codes over a transported named support

The finite local graph may first be given over an abstract old
support P while its prescribed copy in the actual level has old
vertex set Q. Relabel P along an induced equivalence P ≃ Q,
keeping all fresh vertices and their chosen linear order fixed.
The previous theorems preserve the growth class, minimal
strict d-closedness and exact old-neighbour support. Increasing
normalization then gives an admissible ordered code over the
*literal* named support Q.

The only numerical input is a cardinality bound on the complete
local extension, which is unchanged by renaming its old base.
For the particular class C_F the published closure bound
provides this hypothesis; the analytic bound is not
silently assumed or proved here.

Constructing the equivalence P ≃ Q from an arbitrary embedding
of a finite source is the next separate step.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P Q B : Type*}
variable [Fintype P] [DecidableEq P]
variable [Fintype Q] [DecidableEq Q]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- An arbitrary ordered minimal local C_F extension can be
transported to a named isomorphic support Q and included
in the bounded ordered local catalogue there, provided the
uniform size estimate is supplied. -/
theorem bounded_named_growthLocalType
    (F : ℕ → ℝ) (K : ℕ)
    (e : P ≃ Q)
    (H : GraphOn (Sum P B))
    (baseP : GraphOn P) (baseQ : GraphOn Q)
    (hOld : ∀ p q : P,
      H.adj (Sum.inl p) (Sum.inl q) ↔ baseP.adj p q)
    (hBase : ∀ p q : P,
      baseP.adj p q ↔ baseQ.adj (e p) (e q))
    (hGrowth : H.IsGrowthSparse F Finset.univ)
    (hMinimal : H.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ)
    (hExact : H.toPredimension.dClosedHull
      (H.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B)
    (hSize : Fintype.card P + Fintype.card B ≤ K) :
    ∃ code : BoundedOrderedLocalType Q baseQ
        (fun _ G => G.IsGrowthSparse F Finset.univ) K,
      code.1.val = Fintype.card B ∧
      code ∈ catalogue baseQ
        (fun _ G => G.IsGrowthSparse F Finset.univ) K := by
  let J := namedBaseGraph e H
  have hOldQ : ∀ q r : Q,
      J.adj (Sum.inl q) (Sum.inl r) ↔ baseQ.adj q r :=
    fun q r => namedBase_old_adj_iff e H baseP baseQ
      hOld hBase q r
  have hGrowthQ : J.IsGrowthSparse F Finset.univ :=
    (namedBase_growthSparse_iff F e H).mpr hGrowth
  have hMinQ : J.toPredimension.IsMinimalDClosedStep
      (actualOld Q B) Finset.univ :=
    (namedBase_minimal_iff e H).mpr hMinimal
  have hExactQ : J.toPredimension.dClosedHull
      (J.oldNeighbourSet (actualOld Q B) (actualFresh Q B))
      (actualOld Q B) = actualOld Q B :=
    (namedBase_exactSupport_iff e H).mpr hExact
  have hCard : Fintype.card P = Fintype.card Q :=
    Fintype.card_congr e
  have hSizeQ : Fintype.card Q + Fintype.card B ≤ K := by
    simpa only [← hCard] using hSize
  exact bounded_growthLocalType_of_orderedGraph F K
    baseQ J hOldQ hGrowthQ hMinQ hExactQ hSizeQ

end CFLocalCatalogue
end BigHrushovski
