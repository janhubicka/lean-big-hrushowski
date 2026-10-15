import BigHrushovski.CFSelectedClosedSubbatch
import BigHrushovski.CFOrderedCatalogue

/-!
# One-level responses to minimal ordered C_F extension requests

The finite tagged construction attaches every normalized admissible
ordered local code over every literal strictly d-closed old support.
This module extracts the exact response certificate needed for the
countable genericity argument.

The support P of a request may lie inside a larger old d-closed
substructure A. The new block attached to P, together with A,
is d-closed in the *whole* simultaneous level, not merely in
the isolated P-extension. The complete ordered code is induced,
including preservation and reflection of nonedges.

The result is finite and conditional on the caller's local-type
size bound and admissibility predicate. No countable carrier,
extension schedule or Fraïssé identification is asserted here.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The local graph belonging to one request, including the
support and its own new block, is strictly d-closed in the
full simultaneous level. -/
theorem taggedLocal_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedSupport G Allowed bound r ∪
        taggedBlock G Allowed bound r)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  classical
  have h : (levelGraph G Allowed bound).toPredimension.IsDClosed
      (taggedSupport G Allowed bound r ∪
        ({r} : Finset (Requests G Allowed bound)).biUnion
          (taggedBlock G Allowed bound))
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) :=
    taggedSupportClosedSubbatch_dClosed_full G Allowed bound
      {r} (taggedSupport G Allowed bound r)
      (taggedSupport_dClosed_old G Allowed bound r)
      (by
        intro s hs
        have hEq : s = r := by simpa using hs
        subst s
        exact Finset.Subset.rfl)
  simpa using h

/-- Any actual old d-closed source A containing the request's
named support extends with its fresh block to a d-closed copy
inside the full tagged level. This is the finite one-step
genericity response, relative to an arbitrary old source A. -/
theorem taggedResponse_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (a : Finset U)
    (ha : G.toPredimension.IsDClosed a Finset.univ)
    (r : Requests G Allowed bound)
    (hSupport : r.support ⊆ a) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (a.image Sum.inl ∪ taggedBlock G Allowed bound r)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) := by
  classical
  have haOld : (levelGraph G Allowed bound).toPredimension.IsDClosed
      (a.image Sum.inl)
      (taggedOldDomain G Allowed bound) :=
    (G.dClosed_image_iff (levelGraph G Allowed bound)
      Sum.inl Sum.inl_injective
      (fun x y => (levelGraph_old_iff G Allowed bound x y).symm)
      a Finset.univ (Finset.subset_univ _)).mpr ha
  have h : (levelGraph G Allowed bound).toPredimension.IsDClosed
      (a.image Sum.inl ∪
        ({r} : Finset (Requests G Allowed bound)).biUnion
          (taggedBlock G Allowed bound))
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) :=
    taggedSupportClosedSubbatch_dClosed_full G Allowed bound
      {r} (a.image Sum.inl) haOld
      (by
        intro s hs
        have hEq : s = r := by simpa using hs
        subst s
        exact Finset.image_mono _ hSupport)
  simpa using h

/-- Encode a specified named ordered local extension as the
literal tagged-stage request selected by the complete catalogue. -/
def requestOfOrderedLocal
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (P : Finset U)
    (hP : G.toPredimension.IsDClosed P Finset.univ)
    (n : ℕ) (hn : n ≤ bound P)
    (t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (Allowed P) n) :
    Requests G Allowed bound :=
  ⟨P, hP, CFLocalCatalogue.toBounded
    (supportGraph G P) (Allowed P) (bound P) n hn t⟩

theorem requestOfOrderedLocal_mem
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (P : Finset U)
    (hP : G.toPredimension.IsDClosed P Finset.univ)
    (n : ℕ) (hn : n ≤ bound P)
    (t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (Allowed P) n) :
    requestOfOrderedLocal G Allowed bound P hP n hn t ∈
      stageCatalogue G Allowed bound :=
  mem_stageCatalogue G Allowed bound _

/-- Every allowed ordered local type over a named support P
occurs as an induced code, and its new block can be attached
to any old d-closed A containing P while remaining d-closed in
the entire simultaneous level.

This is exactly one minimal extension step. The decomposition
and coherent countable iteration are separate from this lemma. -/
theorem orderedCode_oneLevelResponse
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (a P : Finset U)
    (ha : G.toPredimension.IsDClosed a Finset.univ)
    (hP : G.toPredimension.IsDClosed P Finset.univ)
    (hPA : P ⊆ a)
    (n : ℕ) (hn : n ≤ bound P)
    (t : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier U P) (supportGraph G P)
      (Allowed P) n) :
    let r := requestOfOrderedLocal G Allowed bound P hP n hn t
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (a.image Sum.inl ∪ taggedBlock G Allowed bound r)
      (Finset.univ : Finset (LevelCarrier G Allowed bound)) ∧
    (∀ x y : Sum (SupportCarrier U P) (Fin n),
      t.graph.adj x y ↔
        (levelGraph G Allowed bound).adj
          (localTag G Allowed bound r x)
          (localTag G Allowed bound r y)) := by
  dsimp only
  constructor
  · exact taggedResponse_dClosed_full G Allowed bound a ha
      (requestOfOrderedLocal G Allowed bound P hP n hn t) hPA
  · intro x y
    exact (levelGraph_local_adj_iff G Allowed bound
      (requestOfOrderedLocal G Allowed bound P hP n hn t) x y).symm

end CFStageCatalogue
end BigHrushovski
