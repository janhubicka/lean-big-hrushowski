import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
Finite predimensions and strong-substructure interfaces for The Big Hrushovski.
The edge representation uses *unordered* two-element sets, each counted once.
-/

namespace BigHrushovski

structure FiniteGraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)
  edges_pair : ∀ e ∈ edges, e.card = 2

namespace FiniteGraph

variable {V : Type*} [DecidableEq V]

def edgesWithin (G : FiniteGraph V) (s : Finset V) : Finset (Finset V) :=
  G.edges.filter (fun e => e ⊆ s)

theorem edgesWithin_union_subset (G : FiniteGraph V) (a b : Finset V) :
    G.edgesWithin a ∪ G.edgesWithin b ⊆ G.edgesWithin (a ∪ b) := by
  intro e he
  rcases Finset.mem_union.mp he with ha | hb
  · rcases Finset.mem_filter.mp ha with ⟨hedge, hsub⟩
    exact Finset.mem_filter.mpr ⟨hedge, hsub.trans Finset.subset_union_left⟩
  · rcases Finset.mem_filter.mp hb with ⟨hedge, hsub⟩
    exact Finset.mem_filter.mpr ⟨hedge, hsub.trans Finset.subset_union_right⟩

theorem edgesWithin_inter (G : FiniteGraph V) (a b : Finset V) :
    G.edgesWithin (a ∩ b) = G.edgesWithin a ∩ G.edgesWithin b := by
  ext e
  simp only [edgesWithin, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hedge, hsub⟩
    exact ⟨⟨hedge, hsub.trans Finset.inter_subset_left⟩,
           ⟨hedge, hsub.trans Finset.inter_subset_right⟩⟩
  · rintro ⟨⟨hedge, ha⟩, ⟨_, hb⟩⟩
    refine ⟨hedge, ?_⟩
    intro v hv
    exact Finset.mem_inter.mpr ⟨ha hv, hb hv⟩

theorem edgeCount_supermodular (G : FiniteGraph V) (a b : Finset V) :
    (G.edgesWithin a).card + (G.edgesWithin b).card ≤
      (G.edgesWithin (a ∪ b)).card + (G.edgesWithin (a ∩ b)).card := by
  have hcard := Finset.card_le_card (G.edgesWithin_union_subset a b)
  have hIE := Finset.card_union_add_card_inter (G.edgesWithin a) (G.edgesWithin b)
  rw [G.edgesWithin_inter a b]
  omega

/-- Graph predimension: δ(A) = 2|A| - |E(A)|, with unordered edges. -/
def predim (G : FiniteGraph V) (s : Finset V) : ℤ :=
  2 * (s.card : ℤ) - ((G.edgesWithin s).card : ℤ)

theorem predim_submodular (G : FiniteGraph V) (a b : Finset V) :
    G.predim (a ∪ b) + G.predim (a ∩ b) ≤ G.predim a + G.predim b := by
  have hV := Finset.card_union_add_card_inter a b
  have hE := G.edgeCount_supermodular a b
  unfold predim
  omega

end FiniteGraph

structure Predimension (V : Type*) [DecidableEq V] where
  delta : Finset V → ℤ
  submodular :
    ∀ p q : Finset V, delta (p ∪ q) + delta (p ∩ q) ≤ delta p + delta q

namespace FiniteGraph
def toPredimension {V : Type*} [DecidableEq V] (G : FiniteGraph V) :
    Predimension V where
  delta := G.predim
  submodular := G.predim_submodular
end FiniteGraph

namespace Predimension
variable {V : Type*} [DecidableEq V] (d : Predimension V)

def IsStrong (a b : Finset V) : Prop :=
  a ⊆ b ∧ ∀ c : Finset V, a ⊆ c → c ⊆ b → d.delta a ≤ d.delta c

def IsDClosed (a b : Finset V) : Prop :=
  a ⊆ b ∧
    ∀ c : Finset V, a ⊆ c → c ≠ a → c ⊆ b → d.delta a < d.delta c

theorem strong_refl (a : Finset V) : d.IsStrong a a := by
  refine ⟨Subset.rfl, ?_⟩
  intro c hac hca
  have heq : c = a := le_antisymm hca hac
  subst c
  exact le_refl _

theorem strong_restrict {a b c : Finset V}
    (hac : d.IsStrong a c) (hab : a ⊆ b) (hbc : b ⊆ c) :
    d.IsStrong a b := by
  refine ⟨hab, ?_⟩
  intro x hax hxb
  exact hac.2 x hax (hxb.trans hbc)

theorem strong_of_dClosed {a b : Finset V}
    (hab : d.IsDClosed a b) : d.IsStrong a b := by
  refine ⟨hab.1, ?_⟩
  intro x hax hxb
  by_cases heq : x = a
  · subst x
    exact le_refl _
  · exact le_of_lt (hab.2 x hax heq hxb)

theorem strong_trans {a b c : Finset V}
    (hab : d.IsStrong a b) (hbc : d.IsStrong b c) :
    d.IsStrong a c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro x hax hxc
  have hay : a ⊆ b ∩ x := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hab.1 hv, hax hv⟩
  have hlo : d.delta a ≤ d.delta (b ∩ x) :=
    hab.2 (b ∩ x) hay Finset.inter_subset_left
  have hhi : d.delta b ≤ d.delta (b ∪ x) :=
    hbc.2 (b ∪ x) Finset.subset_union_left (Finset.union_subset hbc.1 hxc)
  have hsub := d.submodular b x
  omega

theorem strong_inter {p q c : Finset V}
    (hp : d.IsStrong p c) (hq : d.IsStrong q c) :
    d.IsStrong (p ∩ q) c := by
  refine ⟨Finset.inter_subset_left.trans hp.1, ?_⟩
  intro x hIx hxc
  have hqbig : d.delta q ≤ d.delta (q ∪ (p ∩ x)) :=
    hq.2 (q ∪ (p ∩ x)) Finset.subset_union_left
      (Finset.union_subset hq.1 (Finset.inter_subset_right.trans hxc))
  have hpbig : d.delta p ≤ d.delta (p ∪ x) :=
    hp.2 (p ∪ x) Finset.subset_union_left (Finset.union_subset hp.1 hxc)
  have hmeet : q ∩ (p ∩ x) = p ∩ q := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hqv, hpX⟩
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpX).1, hqv⟩
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hpv, hqv⟩
      exact Finset.mem_inter.mpr
        ⟨hqv, Finset.mem_inter.mpr ⟨hpv, hIx hv⟩⟩
  have hsub1 := d.submodular q (p ∩ x)
  rw [hmeet] at hsub1
  have hsub2 := d.submodular p x
  omega

end Predimension
end BigHrushovski
