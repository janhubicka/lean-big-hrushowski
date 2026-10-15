import BigHrushovski.CFOrderedNormalization
import BigHrushovski.CFLocalSupportTransport

/-!
# Assemble an ordered C_F local type over an actual named support

Start with a finite linearly ordered new block B, a graph on
P ⊕ B, a minimal strict d-closed step over P and the equation
that P is the exact old-neighbour d-closed support.

The unique increasing enumeration Fin(card B) ≃o B gives a
normalized graph code on P ⊕ Fin(card B). The preceding induced
transport lemmas preserve the complete graph, minimal d-closedness,
and the *entire* old-neighbour support. Hence the normalized graph
is an OrderedLocalType record.

The caller supplies Allowed for the normalized graph explicitly.
Instantiating that condition from the particular growth-function
class C_F, together with its uniform bound, is a separate task.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P B : Type*}
variable [Fintype P] [DecidableEq P]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- Actual old vertices in a graph on P ⊕ B. -/
def actualOld (P : Type*) [Fintype P] [DecidableEq P]
    (B : Type*) [DecidableEq B] : Finset (Sum P B) :=
  (Finset.univ : Finset P).image
    (fun p => (Sum.inl p : Sum P B))

/-- Actual fresh vertices in a graph on P ⊕ B. -/
def actualFresh (P : Type*) [DecidableEq P]
    (B : Type*) [Fintype B] [DecidableEq B] : Finset (Sum P B) :=
  (Finset.univ : Finset B).image
    (fun b => (Sum.inr b : Sum P B))

/-- The increasing tagged enumeration fixes the old part
pointwise as an actual finite vertex set. -/
theorem increasing_old_image :
    (oldVertices P (Fintype.card B)).image
        (taggedIncreasingEquiv (P := P) (B := B)) =
      actualOld P B := by
  classical
  simp only [oldVertices, actualOld, Finset.image_image]
  congr 1
  funext p
  exact taggedIncreasingEquiv_old (P := P) (B := B) p

/-- The fresh part maps bijectively to the whole actual fresh
block, preserving the chosen finite order. -/
theorem increasing_fresh_image :
    (freshVertices P (Fintype.card B)).image
        (taggedIncreasingEquiv (P := P) (B := B)) =
      actualFresh P B := by
  classical
  calc
    (freshVertices P (Fintype.card B)).image
        (taggedIncreasingEquiv (P := P) (B := B)) =
      ((Finset.univ : Finset (Fin (Fintype.card B))).image
        (increasingNewBlock (B := B))).image
          (fun b => (Sum.inr b : Sum P B)) := by
        simp only [freshVertices, Finset.image_image]
        congr 1
        funext i
        exact taggedIncreasingEquiv_new (P := P) (B := B) i
    _ = actualFresh P B := by
      rw [Finset.image_univ_of_surjective
        (increasingNewBlock (B := B)).surjective]
      rfl

/-- A finite ordered actual local extension with exact support
has a canonical normalized local-type code whenever the
externally supplied admissibility predicate holds after
the order-preserving graph relabelling. -/
noncomputable def normalizeOrderedLocalType
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (G : GraphOn (Sum P B))
    (hBase : ∀ p q : P,
      G.adj (Sum.inl p) (Sum.inl q) ↔ base.adj p q)
    (hAllowed : Allowed (Fintype.card B) (orderedNormalizeGraph G))
    (hMin : G.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ)
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B) :
    OrderedLocalType P base Allowed (Fintype.card B) := by
  classical
  let f : Sum P (Fin (Fintype.card B)) ≃ Sum P B :=
    taggedIncreasingEquiv (P := P) (B := B)
  let K := orderedNormalizeGraph G
  let old := oldVertices P (Fintype.card B)
  let fresh := freshVertices P (Fintype.card B)
  have hOld : old.image f = actualOld P B :=
    increasing_old_image (P := P) (B := B)
  have hFresh : fresh.image f = actualFresh P B :=
    increasing_fresh_image (P := P) (B := B)
  have hAll : (Finset.univ :
      Finset (Sum P (Fin (Fintype.card B)))).image f =
      (Finset.univ : Finset (Sum P B)) :=
    Finset.image_univ_of_surjective f.surjective
  have hAdj : ∀ u v : Sum P (Fin (Fintype.card B)),
      K.adj u v ↔ G.adj (f u) (f v) := by
    intro u v
    exact orderedNormalizeGraph_adj_iff G u v
  have hMinNorm : K.toPredimension.IsMinimalDClosedStep
      old (Finset.univ : Finset (Sum P (Fin (Fintype.card B)))) := by
    apply (K.minimalDClosedStep_image_iff G f f.injective
      hAdj old Finset.univ (Finset.subset_univ _)).mp
    rw [hOld, hAll]
    exact hMin
  have hSupportNorm : K.toPredimension.dClosedHull
      (K.oldNeighbourSet old fresh) old = old := by
    have hSupportImage := K.canonicalOldSupport_image G
      f f.injective hAdj old fresh
    rw [hOld, hFresh] at hSupportImage
    apply (Finset.image_injective f.injective)
    calc
      (K.toPredimension.dClosedHull
        (K.oldNeighbourSet old fresh) old).image f =
        G.toPredimension.dClosedHull
          (G.oldNeighbourSet (actualOld P B) (actualFresh P B))
          (actualOld P B) := hSupportImage
      _ = actualOld P B := hSupport
      _ = old.image f := hOld.symm
  refine
    { graph := orderedNormalizeGraph G
      base_agrees := ?_
      allowed := hAllowed
      minimal := hMinNorm
      exact_support := hSupportNorm }
  intro p q
  exact (orderedNormalizeGraph_old_adj G p q).trans (hBase p q)

/-- A normalized record exists and retains literally the complete
increasing pullback of the original finite ordered graph. -/
theorem exists_normalizedOrderedLocalType
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (G : GraphOn (Sum P B))
    (hBase : ∀ p q : P,
      G.adj (Sum.inl p) (Sum.inl q) ↔ base.adj p q)
    (hAllowed : Allowed (Fintype.card B) (orderedNormalizeGraph G))
    (hMin : G.toPredimension.IsMinimalDClosedStep
      (actualOld P B) Finset.univ)
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet (actualOld P B) (actualFresh P B))
      (actualOld P B) = actualOld P B) :
    ∃ t : OrderedLocalType P base Allowed (Fintype.card B),
      t.graph = orderedNormalizeGraph G :=
  ⟨normalizeOrderedLocalType base Allowed G
    hBase hAllowed hMin hSupport, rfl⟩

end CFLocalCatalogue
end BigHrushovski
