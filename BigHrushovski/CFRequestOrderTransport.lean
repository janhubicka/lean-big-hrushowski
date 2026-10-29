import BigHrushovski.CFStageBirthOrderCoherence
import BigHrushovski.CFBlockOrdinalRigidity
import BigHrushovski.CFRequestLexInjection
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
# Transport of the exact C_F request order through a named old embedding

Finite level lifting uses an order-preserving embedding of the already
constructed old part into a later finite stage. The target catalogue
contains the transported literal support and the complete ordered local
graph code. We isolate the resulting order and uniqueness assertions.

The key observation is that lexicographic order on *finite lists*
is preserved and reflected by an order embedding, even for unequal
lengths and proper-prefix comparisons. Thus the support tuples may be
transported without assuming that the old map is surjective.

The remaining fields of a request key are the number of fresh vertices
and the entire ordered adjacency matrix. If these fields are retained,
the exact request comparison is preserved and reflected. Two distinct
source requests cannot collapse to one target request; conversely,
there is at most one target request with a prescribed transported key.

These are conditional transport lemmas. Constructing the transported
request as a member of the actual target catalogue, and simultaneously
assembling all source blocks at a prescribed level, are separate steps.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The usual strict lexicographic list order is transported
exactly by an order embedding, even for unequal lengths. -/
theorem listLt_map_orderEmbedding_iff
    (f : U ↪o V) (xs ys : List U) :
    xs.map f < ys.map f ↔ xs < ys := by
  have hForward : ∀ as bs : List U,
      as < bs → as.map f < bs.map f := by
    intro as bs h
    change List.Lex (· < ·) as bs at h
    change List.Lex (· < ·) (as.map f) (bs.map f)
    induction h with
    | nil => exact List.Lex.nil
    | rel hlt => exact List.Lex.rel (f.strictMono hlt)
    | cons htail ih => exact List.Lex.cons ih
  constructor
  · intro h
    rcases lt_trichotomy xs ys with hlt | heq | hgt
    · exact hlt
    · subst ys
      exact False.elim (lt_irrefl _ h)
    · have hReverse := hForward ys xs hgt
      exact False.elim (lt_asymm hReverse h)
  · exact hForward xs ys

/-- The underlying List.Lex relation has the same transport
property, including the proper-prefix convention. -/
theorem listLex_map_orderEmbedding_iff
    (f : U ↪o V) (xs ys : List U) :
    List.Lex (· < ·) (xs.map f) (ys.map f) ↔
      List.Lex (· < ·) xs ys := by
  change xs.map f < ys.map f ↔ xs < ys
  exact listLt_map_orderEmbedding_iff f xs ys

/-- Equality of mapped lists reflects equality, since an order
embedding is injective. -/
theorem listMap_orderEmbedding_eq_iff
    (f : U ↪o V) (xs ys : List U) :
    xs.map f = ys.map f ↔ xs = ys := by
  constructor
  · intro h
    exact (List.map_injective_iff.mpr f.injective) h
  · intro h
    rw [h]

/-- The increasing tuple of a *literal* image support is exactly
the image of the original increasing tuple. This requires only
an order embedding of old vertices, not surjectivity onto the
target finite stage. -/
theorem requestSupportTuple_of_namedImage
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (hSupport : t.support = r.support.map f.toEmbedding) :
    requestSupportTuple H AllowedV boundV t =
      (requestSupportTuple G AllowedU boundU r).map f := by
  classical
  change t.support.sort (· ≤ ·) =
    (r.support.sort (· ≤ ·)).map f
  rw [hSupport]
  have hf : StrictMonoOn (f : U → V) r.support :=
    fun _ _ _ _ hab => f.strictMono hab
  exact (hf.map_finsetSort).symm

/-- Exact transport of a request key. Its target support tuple
uses the actual target vertex names; its fresh size and complete
adjacency matrix are unchanged. This is a predicate rather than
an assertion that the transported request already exists. -/
structure RequestCodeTransport
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV) : Prop where
  support_tuple :
    requestSupportTuple H AllowedV boundV t =
      (requestSupportTuple G AllowedU boundU r).map f
  fresh_size : t.code.1.val = r.code.1.val
  adjacency_code :
    requestAdjacencyCode H AllowedV boundV t =
      requestAdjacencyCode G AllowedU boundU r

/-- Literal image of the named support plus equality of the
fresh size and complete graph matrix supplies the exact key
transport certificates. -/
theorem requestCodeTransport_of_namedImage
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (hSupport : t.support = r.support.map f.toEmbedding)
    (hSize : t.code.1.val = r.code.1.val)
    (hAdj : requestAdjacencyCode H AllowedV boundV t =
      requestAdjacencyCode G AllowedU boundU r) :
    RequestCodeTransport G H AllowedU AllowedV boundU boundV f r t :=
  ⟨requestSupportTuple_of_namedImage G H AllowedU AllowedV
      boundU boundV f r t hSupport, hSize, hAdj⟩

/-- Transporting two complete literal request codes preserves and
reflects their *precise* lexicographic order, not merely their
abstract isomorphism types or their fresh-block sizes. -/
theorem requestLexLt_transport_iff
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r s : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (hr : RequestCodeTransport G H AllowedU AllowedV boundU boundV f r t)
    (hs : RequestCodeTransport G H AllowedU AllowedV boundU boundV f s u) :
    RequestLexLt G AllowedU boundU r s ↔
      RequestLexLt H AllowedV boundV t u := by
  dsimp only [RequestLexLt]
  rw [hr.support_tuple, hs.support_tuple,
    hr.fresh_size, hs.fresh_size,
    hr.adjacency_code, hs.adjacency_code]
  simp only [listLt_map_orderEmbedding_iff, listMap_orderEmbedding_eq_iff]

/-- A prescribed source request has *at most one* target request
with its complete transported named key. -/
theorem requestCodeTransport_unique
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (ht : RequestCodeTransport G H AllowedU AllowedV boundU boundV f r t)
    (hu : RequestCodeTransport G H AllowedU AllowedV boundU boundV f r u) :
    t = u := by
  apply requestLexKey_injective H AllowedV boundV
  exact Prod.ext (ht.support_tuple.trans hu.support_tuple.symm)
    (Prod.ext (ht.fresh_size.trans hu.fresh_size.symm)
      (ht.adjacency_code.trans hu.adjacency_code.symm))

/-- Distinct source requests cannot collapse under complete
transport through an order embedding. This is the finite
distinctness input for the simultaneous target block batch. -/
theorem requestCodeTransport_reflects_eq
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (f : U ↪o V)
    (r s : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (hr : RequestCodeTransport G H AllowedU AllowedV boundU boundV f r t)
    (hs : RequestCodeTransport G H AllowedU AllowedV boundU boundV f s u)
    (htu : t = u) :
    r = s := by
  by_contra hne
  rcases requestLexLt_strict_total G AllowedU boundU r s hne with hrs | hsr
  · have hts := (requestLexLt_transport_iff G H AllowedU AllowedV
      boundU boundV f r s t u hr hs).mp hrs
    subst u
    exact requestLexLt_irrefl H AllowedV boundV t hts
  · have hst := (requestLexLt_transport_iff G H AllowedU AllowedV
      boundU boundV f s r u t hs hr).mp hsr
    subst u
    exact requestLexLt_irrefl H AllowedV boundV t hst

end CFStageCatalogue
end BigHrushovski
