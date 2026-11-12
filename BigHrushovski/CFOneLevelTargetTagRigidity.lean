import BigHrushovski.CFBirthLocalCodeInduced
import BigHrushovski.CFCompleteLocalCodeTransport
import BigHrushovski.CFPartialRequestUniqueness

/-!
# Unique target request tag from induced local coordinate maps

For finite unique C_F level lifting, one must compare the actual
target request of an ARBITRARY embedding with the canonical
request constructed over the earlier source images.

We first identify the complete ordered adjacency matrix of
any target request reached by a genuinely partial map of one
source local carrier. The hypotheses describe only how that
partial map acts on the named old support and each fresh ordinal;
it must preserve and reflect all edges on those coordinates.
The previously proved induced local graph theorem converts
these ambient edge comparisons into equality of the complete
ordered request matrices, including nonedges.

If two such target requests lie at the same target level, have
the same literal old support and fresh size, they are the SAME
literal request. No code equality is assumed: it follows from
the two induced local maps.

The remaining step for general finite embedding uniqueness is
to construct these partial coordinate maps directly from b/RH
value preservation, the canonical order, and agreement on all
earlier source vertices. These theorems do not assume or prove
that missing step or an induction across levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Complete local coordinates of the actual tagged request,
with no abstract renumbering of its support or fresh ordinal. -/
abbrev BirthRequestLocalCarrier
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :=
  Sum (SupportCarrier (stage F K n).carrier r.support)
    (Fin r.code.1.val)

/-- A local request coordinate has one literal vertex of the
countable birth-labelled graph, obtained through the actual
finite-stage injection. -/
noncomputable def birthRequestLocalVertex
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    BirthRequestLocalCarrier F K n r → Vertex F K :=
  fun a =>
    toVertex F K (n + 1)
      (localTag (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r a)

/-- Any partial local map induced on ALL the source request
coordinates, and agreeing with the target's literal ordered
support/fresh-coordinate map, preserves the COMPLETE ordered
adjacency matrix. This includes old–old, old–fresh and
fresh–fresh comparisons and every corresponding nonedge. -/
theorem birthRequest_adjacencyCode_eq_of_partialInduced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ)
    [LinearOrder (stage F K n).carrier]
    [LinearOrder (stage F K m).carrier]
    (r : BirthRequest F K n)
    (t : BirthRequest F K m)
    (oldIso : SupportCarrier (stage F K n).carrier r.support ≃o
      SupportCarrier (stage F K m).carrier t.support)
    (freshIso : Fin r.code.1.val ≃o Fin t.code.1.val)
    (e : BirthRequestLocalCarrier F K n r → Vertex F K)
    (hTarget : ∀ a : BirthRequestLocalCarrier F K n r,
      e a = birthRequestLocalVertex F K m t
        (Sum.map oldIso freshIso a))
    (hInduced : ∀ a b : BirthRequestLocalCarrier F K n r,
      (countableGraph F K).adj
        (birthRequestLocalVertex F K n r a)
        (birthRequestLocalVertex F K n r b) ↔
      (countableGraph F K).adj (e a) (e b)) :
    requestAdjacencyCode (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r =
    requestAdjacencyCode (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card) t := by
  apply requestAdjacencyCode_eq_of_localOrderIso
    (stage F K n).graph (stage F K m).graph
    (GrowthAllowedLocal F) (GrowthAllowedLocal F)
    (fun P => K P.card) (fun P => K P.card)
    r t oldIso freshIso
  intro a b
  calc
    r.code.2.graph.adj a b ↔
        (countableGraph F K).adj
          (birthRequestLocalVertex F K n r a)
          (birthRequestLocalVertex F K n r b) :=
      (birthRequest_localAdj_iff F K n r a b).symm
    _ ↔ (countableGraph F K).adj (e a) (e b) :=
      hInduced a b
    _ ↔ (countableGraph F K).adj
          (birthRequestLocalVertex F K m t
            (Sum.map oldIso freshIso a))
          (birthRequestLocalVertex F K m t
            (Sum.map oldIso freshIso b)) := by
      rw [hTarget a, hTarget b]
    _ ↔ t.code.2.graph.adj
          (Sum.map oldIso freshIso a)
          (Sum.map oldIso freshIso b) :=
      birthRequest_localAdj_iff F K m t
        (Sum.map oldIso freshIso a)
        (Sum.map oldIso freshIso b)

/-- Two target request tags of the same target level are
necessarily equal once they have the same literal named
support, same fresh size, and both are reached by induced
partial coordinate maps from the same complete source request.

The full adjacency-code equality is DERIVED, not a premise.
The two coordinate maps may be independently defined and
need not coincide outside this one source local interval. -/
theorem birthRequest_targetTag_unique_of_partialInduced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ)
    [LinearOrder (stage F K n).carrier]
    [LinearOrder (stage F K m).carrier]
    (r : BirthRequest F K n)
    (t₁ t₂ : BirthRequest F K m)
    (hSupport : t₁.support = t₂.support)
    (hSize : t₁.code.1.val = t₂.code.1.val)
    (oldIso₁ : SupportCarrier (stage F K n).carrier r.support ≃o
      SupportCarrier (stage F K m).carrier t₁.support)
    (oldIso₂ : SupportCarrier (stage F K n).carrier r.support ≃o
      SupportCarrier (stage F K m).carrier t₂.support)
    (freshIso₁ : Fin r.code.1.val ≃o Fin t₁.code.1.val)
    (freshIso₂ : Fin r.code.1.val ≃o Fin t₂.code.1.val)
    (e₁ e₂ : BirthRequestLocalCarrier F K n r → Vertex F K)
    (hTarget₁ : ∀ a : BirthRequestLocalCarrier F K n r,
      e₁ a = birthRequestLocalVertex F K m t₁
        (Sum.map oldIso₁ freshIso₁ a))
    (hTarget₂ : ∀ a : BirthRequestLocalCarrier F K n r,
      e₂ a = birthRequestLocalVertex F K m t₂
        (Sum.map oldIso₂ freshIso₂ a))
    (hInduced₁ : ∀ a b : BirthRequestLocalCarrier F K n r,
      (countableGraph F K).adj
        (birthRequestLocalVertex F K n r a)
        (birthRequestLocalVertex F K n r b) ↔
      (countableGraph F K).adj (e₁ a) (e₁ b))
    (hInduced₂ : ∀ a b : BirthRequestLocalCarrier F K n r,
      (countableGraph F K).adj
        (birthRequestLocalVertex F K n r a)
        (birthRequestLocalVertex F K n r b) ↔
      (countableGraph F K).adj (e₂ a) (e₂ b)) :
    t₁ = t₂ := by
  have hCode₁ :=
    birthRequest_adjacencyCode_eq_of_partialInduced
      F K n m r t₁ oldIso₁ freshIso₁ e₁ hTarget₁ hInduced₁
  have hCode₂ :=
    birthRequest_adjacencyCode_eq_of_partialInduced
      F K n m r t₂ oldIso₂ freshIso₂ e₂ hTarget₂ hInduced₂
  exact request_eq_of_support_size_adjacency
    (stage F K m).graph (GrowthAllowedLocal F)
    (fun P => K P.card) t₁ t₂
    hSupport hSize (hCode₁.symm.trans hCode₂)

end CFCoherentTower
end BigHrushovski
