import BigHrushovski.OrientationRelativeStrong
import Mathlib.Tactic

/-!
# A literal finite sink-star orientation extension

Given a finite two-orientation O and a set U of old vertices,
adjoin one new sink z and a distinct vertex x_a for each a in U.
Put exactly the two arrows x_a → a and x_a → z. Old outgoing
neighbour sets are unchanged.

This is the concrete finite orientation underlying the sink-graph
Rado extension argument for N_F in Section 7.4.5 of the manuscript.
The construction is a valid two-orientation and the old part is
successor-closed, hence predimension-strong. In the actual N_F
application U consists of old sinks.

The *strict* successor-d-closed extension assertion in the
manuscript does not follow merely from successor-closedness. Its
separate proof uses all growth-function inequalities and the exact
relative predimension calculation; neither is claimed here.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V]

/-- The old vertices, a new sink (none), and one new predecessor
for each indexed member of U (some a). -/
abbrev SinkStarVertex (U : Finset V) :=
  V ⊕ Option {a : V // a ∈ U}

/-- Complete outgoing neighbour relation on the star extension. -/
def sinkStarOut (O : FiniteOrientation V) (U : Finset V) :
    SinkStarVertex U → Finset (SinkStarVertex U)
  | Sum.inl a => (O.out a).image Sum.inl
  | Sum.inr none => ∅
  | Sum.inr (some a) => {Sum.inl a.val, Sum.inr none}

/-- The star construction is a *genuine two-orientation*: no new
loop, reverse arrow, or outdegree violation is introduced. -/
noncomputable def sinkStarExtension (O : FiniteOrientation V)
    (U : Finset V) : FiniteOrientation (SinkStarVertex U) := by
  classical
  refine {
    out := O.sinkStarOut U
    noLoop := ?_
    noOpposite := ?_
    outDegreeTwo := ?_
  }
  · intro x
    cases x with
    | inl a =>
      change Sum.inl a ∉ (O.out a).image Sum.inl
      intro h
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
      have heq : b = a := Sum.inl_injective hba
      subst b
      exact O.noLoop a hb
    | inr o =>
      cases o with
      | none => simp [sinkStarOut]
      | some u => simp [sinkStarOut]
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        change Sum.inl b ∈ (O.out a).image Sum.inl at hxy
        have hab : b ∈ O.out a := by
          obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hxy
          have heq : c = b := Sum.inl_injective hcb
          simpa [heq] using hc
        change Sum.inl a ∉ (O.out b).image Sum.inl
        intro hba
        obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp hba
        have heq : c = a := Sum.inl_injective hca
        have hba' : a ∈ O.out b := by simpa [heq] using hc
        exact O.noOpposite a b hab hba'
      | inr o =>
        change Sum.inr o ∈ (O.out a).image Sum.inl at hxy
        obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hxy
        cases hcb
    | inr o =>
      cases o with
      | none =>
        change y ∈ (∅ : Finset (SinkStarVertex U)) at hxy
        simp at hxy
      | some u =>
        change y ∈ ({Sum.inl u.val, Sum.inr none} :
          Finset (SinkStarVertex U)) at hxy
        have hcases : y = Sum.inl u.val ∨ y = Sum.inr none := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hxy
        rcases hcases with h | h
        · subst y
          change Sum.inr (some u) ∉ (O.out u.val).image Sum.inl
          intro h
          obtain ⟨v, hv, hbad⟩ := Finset.mem_image.mp h
          cases hbad
        · subst y
          change Sum.inr (some u) ∉ (∅ : Finset (SinkStarVertex U))
          simp
  · intro x
    cases x with
    | inl a =>
      change ((O.out a).image (Sum.inl : V → SinkStarVertex U)).card ≤ 2
      have hImage : ((O.out a).image
          (Sum.inl : V → SinkStarVertex U)).card =
          (O.out a).card := by
        apply Finset.card_image_iff.mpr
        intro x hx y hy h
        exact Sum.inl_injective h
      rw [hImage]
      exact O.outDegreeTwo a
    | inr o =>
      cases o with
      | none => simp [sinkStarOut]
      | some u => simp [sinkStarOut]

/-- The new distinguished point z is a sink. -/
def sinkStarNewSink (U : Finset V) : SinkStarVertex U :=
  Sum.inr none

/-- The new predecessor indexed by a ∈ U. -/
def sinkStarArm (U : Finset V) (a : {a : V // a ∈ U}) :
    SinkStarVertex U :=
  Sum.inr (some a)

theorem sinkStar_newSink_isSink (O : FiniteOrientation V)
    (U : Finset V) :
    (O.sinkStarExtension U).IsSink (sinkStarNewSink U) := by
  rfl

/-- Every new predecessor has exactly the two required outgoing
neighbours, with no arbitrary ordering of those neighbours. -/
theorem sinkStar_arm_out (O : FiniteOrientation V)
    (U : Finset V) (a : {a : V // a ∈ U}) :
    (O.sinkStarExtension U).out (sinkStarArm U a) =
      ({Sum.inl a.val, sinkStarNewSink U} :
        Finset (SinkStarVertex U)) := by
  rfl

/-- The original complete outgoing value is unchanged. -/
theorem sinkStar_old_out (O : FiniteOrientation V)
    (U : Finset V) (a : V) :
    (O.sinkStarExtension U).out (Sum.inl a) =
      (O.out a).image Sum.inl := by
  rfl

/-- The original directed adjacency relation is preserved and
reflected on all pairs of old vertices. -/
theorem sinkStar_old_arrow_iff (O : FiniteOrientation V)
    (U : Finset V) (a b : V) :
    (Sum.inl b : SinkStarVertex U) ∈
      (O.sinkStarExtension U).out (Sum.inl a) ↔
      b ∈ O.out a := by
  rw [O.sinkStar_old_out U a]
  constructor
  · intro h
    obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp h
    have heq : c = b := Sum.inl_injective hcb
    simpa [heq] using hc
  · intro h
    exact Finset.mem_image.mpr ⟨b, h, rfl⟩

theorem sinkStar_old_adj_iff (O : FiniteOrientation V)
    (U : Finset V) (a b : V) :
    (O.sinkStarExtension U).Adjacent (Sum.inl a) (Sum.inl b) ↔
      O.Adjacent a b := by
  simp only [Adjacent, O.sinkStar_old_arrow_iff U]

/-- Actual old vertices form a successor-closed induced domain in
the extended orientation. In particular there are no arrows with
an old tail and a new endpoint. -/
noncomputable def sinkStarOldCarrier [Fintype V]
    (U : Finset V) : Finset (SinkStarVertex U) := by
  classical
  exact (Finset.univ : Finset V).image Sum.inl

theorem sinkStar_old_successorClosed [Fintype V]
    (O : FiniteOrientation V) (U : Finset V) :
    (O.sinkStarExtension U).IsSuccessorClosed
      (sinkStarOldCarrier U) := by
  classical
  intro x hx y hy
  change x ∈ (Finset.univ : Finset V).image Sum.inl at hx
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  rw [O.sinkStar_old_out U a] at hy
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  change Sum.inl b ∈ (Finset.univ : Finset V).image Sum.inl
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩

/-- The old part is predimension-strong by the edge-tail bound.
This is only ordinary strongness, not strict F d-closure. -/
theorem sinkStar_old_strong [Fintype V]
    (O : FiniteOrientation V) (U : Finset V) :
    (O.sinkStarExtension U).underlying.toPredimension.IsStrong
      (sinkStarOldCarrier U) Finset.univ := by
  apply (O.sinkStarExtension U).successorClosed_strong
  · exact Finset.subset_univ _
  · exact O.sinkStar_old_successorClosed U

end FiniteOrientation
end BigHrushovski
