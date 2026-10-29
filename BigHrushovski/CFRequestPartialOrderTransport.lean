import BigHrushovski.CFRequestOrderTransport

/-!
# Exact request comparison over a selected finite old source

In finite level lifting the previously defined map is only specified
on a finite closed subset S of the old source stage, not on the
whole old stage. The target stage can be earlier and smaller, so
there may be no order embedding of the entire source stage.

For comparing the requests of the selected source blocks it suffices
that a map f preserve strict order on S. Every support involved lies
in S. The exact lexicographic order of the support tuples is then
preserved and reflected even when f is not increasing outside S.

The target request records still have to be constructed separately
from the induced named local graphs. This module proves the order
and uniqueness statements conditional on the exact transported
support tuples, sizes, and full adjacency matrices.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Lexicographic order on lists whose entries lie in S is
preserved and reflected by a map strictly increasing *on S*.
No global injectivity or order-preservation assumption is made. -/
theorem listLt_map_strictMonoOn_iff
    (f : U → V) (S : Finset U)
    (hf : StrictMonoOn f S)
    (xs ys : List U)
    (hxs : ∀ x ∈ xs, x ∈ S)
    (hys : ∀ y ∈ ys, y ∈ S) :
    xs.map f < ys.map f ↔ xs < ys := by
  have hForward : ∀ (as bs : List U),
      (∀ x ∈ as, x ∈ S) →
      (∀ y ∈ bs, y ∈ S) →
      as < bs → as.map f < bs.map f := by
    intro as bs has hbs h
    change List.Lex (· < ·) as bs at h
    change List.Lex (· < ·) (as.map f) (bs.map f)
    revert has hbs
    induction h with
    | nil =>
        intro _ _
        exact List.Lex.nil
    | rel hlt =>
        intro has hbs
        apply List.Lex.rel
        exact hf (has _ (by simp)) (hbs _ (by simp)) hlt
    | cons htail ih =>
        intro has hbs
        apply List.Lex.cons
        apply ih
        · intro x hx
          exact has x (by simp [hx])
        · intro y hy
          exact hbs y (by simp [hy])
  constructor
  · intro h
    rcases lt_trichotomy xs ys with hlt | heq | hgt
    · exact hlt
    · subst ys
      exact False.elim (lt_irrefl _ h)
    · have hReverse := hForward ys xs hys hxs hgt
      exact False.elim (lt_asymm hReverse h)
  · exact hForward xs ys hxs hys

/-- Equality of mapped lists reflects equality on the selected
finite old source, even when f is arbitrary elsewhere. -/
theorem listMap_eq_strictMonoOn_iff
    (f : U → V) (S : Finset U)
    (hf : StrictMonoOn f S)
    (xs ys : List U)
    (hxs : ∀ x ∈ xs, x ∈ S)
    (hys : ∀ y ∈ ys, y ∈ S) :
    xs.map f = ys.map f ↔ xs = ys := by
  constructor
  · intro h
    rcases lt_trichotomy xs ys with hlt | heq | hgt
    · have hm := (listLt_map_strictMonoOn_iff
        f S hf xs ys hxs hys).mpr hlt
      rw [h] at hm
      exact False.elim (lt_irrefl _ hm)
    · exact heq
    · have hm := (listLt_map_strictMonoOn_iff
        f S hf ys xs hys hxs).mpr hgt
      rw [h] at hm
      exact False.elim (lt_irrefl _ hm)
  · intro h
    rw [h]

/-- A request whose named support lies in S has all entries of
its increasing support tuple in S. -/
theorem requestSupportTuple_subset_of_support_subset
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound)
    (S : Finset U) (h : r.support ⊆ S) :
    ∀ x ∈ requestSupportTuple G Allowed bound r, x ∈ S := by
  intro x hx
  apply h
  change x ∈ r.support.sort (· ≤ ·) at hx
  simpa only [Finset.mem_sort] using hx

/-- Exact transported request code over a selected finite old
source S. The total function f is only required to be increasing
on S; its values outside S are irrelevant. -/
structure RequestCodeTransportOn
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV) : Prop where
  support_subset : r.support ⊆ S
  support_tuple :
    requestSupportTuple H AllowedV boundV t =
      (requestSupportTuple G AllowedU boundU r).map f
  fresh_size : t.code.1.val = r.code.1.val
  adjacency_code :
    requestAdjacencyCode H AllowedV boundV t =
      requestAdjacencyCode G AllowedU boundU r

/-- The exact request order is transported by a map increasing
only on the selected old source, provided both supports lie there
and the complete transported codes are given. -/
theorem requestLexLt_transportOn_iff
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V) (hf : StrictMonoOn f S)
    (r s : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (hr : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f r t)
    (hs : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f s u) :
    RequestLexLt G AllowedU boundU r s ↔
      RequestLexLt H AllowedV boundV t u := by
  have hR := requestSupportTuple_subset_of_support_subset
    G AllowedU boundU r S hr.support_subset
  have hS := requestSupportTuple_subset_of_support_subset
    G AllowedU boundU s S hs.support_subset
  have hLt := listLt_map_strictMonoOn_iff f S hf
    (requestSupportTuple G AllowedU boundU r)
    (requestSupportTuple G AllowedU boundU s) hR hS
  have hEq := listMap_eq_strictMonoOn_iff f S hf
    (requestSupportTuple G AllowedU boundU r)
    (requestSupportTuple G AllowedU boundU s) hR hS
  dsimp only [RequestLexLt]
  rw [hr.support_tuple, hs.support_tuple,
    hr.fresh_size, hs.fresh_size,
    hr.adjacency_code, hs.adjacency_code]
  simp only [hLt, hEq]

/-- A complete key over the selected old source determines
at most one target request, even though the old map need not
be increasing outside that source. -/
theorem requestCodeTransportOn_unique
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V)
    (r : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (ht : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f r t)
    (hu : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f r u) :
    t = u := by
  apply requestLexKey_injective H AllowedV boundV
  exact Prod.ext (ht.support_tuple.trans hu.support_tuple.symm)
    (Prod.ext (ht.fresh_size.trans hu.fresh_size.symm)
      (ht.adjacency_code.trans hu.adjacency_code.symm))

/-- Distinct source requests whose supports lie in S cannot
collapse to one target request under complete key transport. -/
theorem requestCodeTransportOn_reflects_eq
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V) (hf : StrictMonoOn f S)
    (r s : StageRequest G AllowedU boundU)
    (t u : StageRequest H AllowedV boundV)
    (hr : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f r t)
    (hs : RequestCodeTransportOn G H AllowedU AllowedV boundU boundV S f s u)
    (htu : t = u) :
    r = s := by
  by_contra hne
  rcases requestLexLt_strict_total G AllowedU boundU r s hne with hrs | hsr
  · have hts := (requestLexLt_transportOn_iff G H AllowedU AllowedV
      boundU boundV S f hf r s t u hr hs).mp hrs
    subst u
    exact requestLexLt_irrefl H AllowedV boundV t hts
  · have hst := (requestLexLt_transportOn_iff G H AllowedU AllowedV
      boundU boundV S f hf s r u t hs hr).mp hsr
    subst u
    exact requestLexLt_irrefl H AllowedV boundV t hst

end CFStageCatalogue
end BigHrushovski
