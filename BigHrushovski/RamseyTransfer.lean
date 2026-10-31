import Mathlib

/-!
# Ramsey transfers for the Big Hrushovski manuscript

These are conditional combinatorial transfer lemmas, not a construction of
either the C0 coordinate host or the CF unique level lifts.  The full
embedding-to-coordinate equivalence, and equivariance under postcomposition,
are assumptions that must be proved separately for the concrete structures.

The coordinate-host lemma is deliberately weaker: the return map is only
used on composites known to represent valid self-embeddings.
-/

namespace BigHrushovski
namespace RamseyTransfer

/-- The embedding-colouring formulation of a big Ramsey upper bound.
Concrete applications must show that the action is postcomposition by
genuine self-embeddings. -/
def DegreeAtMost (Emb Self : Type*) (action : Self → Emb → Emb)
    (degree : ℕ) : Prop :=
  ∀ (r : ℕ) (colour : Emb → Fin r),
    ∃ s : Self, ∃ palette : Finset (Fin r),
      palette.card ≤ degree ∧ ∀ e : Emb, colour (action s e) ∈ palette

/-- An equivariant pair of bijections preserves every upper bound. -/
theorem degreeAtMost_forward
    {Emb Coord Self SelfCoord : Type*}
    (embEquiv : Emb ≃ Coord)
    (selfEquiv : Self ≃ SelfCoord)
    (action : Self → Emb → Emb)
    (coordinateAction : SelfCoord → Coord → Coord)
    (hcompat : ∀ (s : Self) (e : Emb),
      embEquiv (action s e) =
        coordinateAction (selfEquiv s) (embEquiv e))
    {degree : ℕ}
    (h : DegreeAtMost Emb Self action degree) :
    DegreeAtMost Coord SelfCoord coordinateAction degree := by
  intro r colour
  obtain ⟨s, palette, hcard, hpalette⟩ :=
    h r (fun e => colour (embEquiv e))
  refine ⟨selfEquiv s, palette, hcard, ?_⟩
  intro f
  obtain ⟨e, rfl⟩ := embEquiv.surjective f
  simpa only [hcompat s e] using hpalette e

/-- Equality of all upper bounds, not just the direction needed for
the upper-bound argument. In particular lower bounds are preserved. -/
theorem degreeAtMost_iff
    {Emb Coord Self SelfCoord : Type*}
    (embEquiv : Emb ≃ Coord)
    (selfEquiv : Self ≃ SelfCoord)
    (action : Self → Emb → Emb)
    (coordinateAction : SelfCoord → Coord → Coord)
    (hcompat : ∀ (s : Self) (e : Emb),
      embEquiv (action s e) =
        coordinateAction (selfEquiv s) (embEquiv e))
    (degree : ℕ) :
    DegreeAtMost Emb Self action degree ↔
      DegreeAtMost Coord SelfCoord coordinateAction degree := by
  constructor
  · exact degreeAtMost_forward embEquiv selfEquiv action
      coordinateAction hcompat
  · intro h
    have hreverse : ∀ (t : SelfCoord) (f : Coord),
        embEquiv.symm (coordinateAction t f) =
          action (selfEquiv.symm t) (embEquiv.symm f) := by
      intro t f
      simpa using
        (congrArg embEquiv.symm
          (hcompat (selfEquiv.symm t) (embEquiv.symm f))).symm
    exact degreeAtMost_forward embEquiv.symm selfEquiv.symm
      coordinateAction action hreverse h

/-- The exact least bound, including all smaller-degree obstructions. -/
def ExactDegree (Emb Self : Type*) (action : Self → Emb → Emb)
    (degree : ℕ) : Prop :=
  DegreeAtMost Emb Self action degree ∧
    ∀ smaller : ℕ, smaller < degree →
      ¬ DegreeAtMost Emb Self action smaller

theorem exactDegree_iff
    {Emb Coord Self SelfCoord : Type*}
    (embEquiv : Emb ≃ Coord)
    (selfEquiv : Self ≃ SelfCoord)
    (action : Self → Emb → Emb)
    (coordinateAction : SelfCoord → Coord → Coord)
    (hcompat : ∀ (s : Self) (e : Emb),
      embEquiv (action s e) =
        coordinateAction (selfEquiv s) (embEquiv e))
    (degree : ℕ) :
    ExactDegree Emb Self action degree ↔
      ExactDegree Coord SelfCoord coordinateAction degree := by
  constructor
  · rintro ⟨hbound, hminimal⟩
    refine ⟨(degreeAtMost_iff embEquiv selfEquiv action
      coordinateAction hcompat degree).mp hbound, ?_⟩
    intro smaller hlt hsmall
    exact hminimal smaller hlt
      ((degreeAtMost_iff embEquiv selfEquiv action
        coordinateAction hcompat smaller).mpr hsmall)
  · rintro ⟨hbound, hminimal⟩
    refine ⟨(degreeAtMost_iff embEquiv selfEquiv action
      coordinateAction hcompat degree).mpr hbound, ?_⟩
    intro smaller hlt hsmall
    exact hminimal smaller hlt
      ((degreeAtMost_iff embEquiv selfEquiv action
        coordinateAction hcompat smaller).mp hsmall)

/-- Finite embeddings can be identified with increasing level tuples.
This is the uniform Ramsey transfer for both the omega-level tower
and the rational homogeneous limit, conditional on unique level lifts. -/
theorem levelDegree_iff
    {Emb Self Level : Type*} [LinearOrder Level]
    (m : ℕ)
    (tuple : Emb ≃ (Fin m ↪o Level))
    (levels : Self ≃ (Level ↪o Level))
    (action : Self → Emb → Emb)
    (hcompat : ∀ (s : Self) (e : Emb),
      tuple (action s e) = (tuple e).trans (levels s))
    (degree : ℕ) :
    DegreeAtMost Emb Self action degree ↔
      DegreeAtMost (Fin m ↪o Level) (Level ↪o Level)
        (fun h e => e.trans h) degree :=
  degreeAtMost_iff tuple levels action (fun h e => e.trans h)
    hcompat degree

/-- The optimal-degree version used in the Devlin reduction. -/
theorem exactLevelDegree_iff
    {Emb Self Level : Type*} [LinearOrder Level]
    (m : ℕ)
    (tuple : Emb ≃ (Fin m ↪o Level))
    (levels : Self ≃ (Level ↪o Level))
    (action : Self → Emb → Emb)
    (hcompat : ∀ (s : Self) (e : Emb),
      tuple (action s e) = (tuple e).trans (levels s))
    (degree : ℕ) :
    ExactDegree Emb Self action degree ↔
      ExactDegree (Fin m ↪o Level) (Level ↪o Level)
        (fun h e => e.trans h) degree :=
  exactDegree_iff tuple levels action (fun h e => e.trans h)
    hcompat degree

/-- Upper bounds transfer from a coordinate host by an actual return
map. No false isomorphism between the host and the structure is assumed. -/
theorem degreeAtMost_of_coordinateHost
    {Emb Host Self HostSelf : Type*}
    (action : Self → Emb → Emb)
    (hostAction : HostSelf → Host → Host)
    (encode : Emb → Host)
    (returnMap : Host → Emb)
    (copy : HostSelf → Self)
    (hcompat : ∀ (s : HostSelf) (e : Emb),
      action (copy s) e = returnMap (hostAction s (encode e)))
    {degree : ℕ}
    (h : DegreeAtMost Host HostSelf hostAction degree) :
    DegreeAtMost Emb Self action degree := by
  intro r colour
  obtain ⟨s, palette, hcard, hpalette⟩ :=
    h r (fun w => colour (returnMap w))
  refine ⟨copy s, palette, hcard, ?_⟩
  intro e
  simpa only [hcompat s e] using hpalette (encode e)

/-- Negative-control setup: a singleton under the identity action has
degree at most one. -/
theorem singleton_degree_one :
    DegreeAtMost Unit Unit (fun _ x => x) 1 := by
  intro r colour
  refine ⟨(), {colour ()}, by simp, ?_⟩
  intro x
  cases x
  simp

/-- Negative control: two embeddings can have one identical level
coordinate and nonetheless carry two unavoidable colours. A surjective
level map without uniqueness does NOT justify the transfer. -/
theorem two_unseparated_lifts_not_degree_one :
    ¬ DegreeAtMost Bool Unit (fun _ b => b) 1 := by
  intro h
  obtain ⟨_, palette, hcard, hpalette⟩ :=
    h 2 (fun b => if b then (1 : Fin 2) else 0)
  have hfalse : (0 : Fin 2) ∈ palette := by
    simpa using hpalette false
  have htrue : (1 : Fin 2) ∈ palette := by
    simpa using hpalette true
  have hpair : ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) ⊆ palette := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hzero | hone
    · simpa [hzero] using hfalse
    · simpa [hone] using htrue
  have htwo : 2 ≤ palette.card := by
    calc
      2 = ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)).card := by decide
      _ ≤ palette.card := Finset.card_le_card hpair
  omega

end RamseyTransfer
end BigHrushovski
