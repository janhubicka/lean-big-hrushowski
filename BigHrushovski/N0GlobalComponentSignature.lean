import BigHrushovski.N0CanonicalLocalFibres
import BigHrushovski.N0GlobalOrderSurjectivity
import Mathlib.Tactic

/-!
# Finite component-order signatures and inherited successor-closure orders

A successor-first enumeration need not be presented by a global
lexicographic construction. Nevertheless every vertex in the lower
successor part P_B of an actual SCC B precedes every vertex in B.
Consequently P_B is an initial segment of the induced ordering on C_B.

A component-interval enumeration of the labelled vertices is determined
uniquely by its component ranking and its pairwise comparisons *inside*
individual SCCs. The signature below records precisely that information;
comparisons between distinct SCCs are recovered from the component ranking.

These finite statements give the injective half of the intended global
canonical-order encoding. No claim of the required surjectivity or of the
Ramsey theorem is made.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- In every actual successor-first enumeration, the strict successor
part P_B comes before the whole top SCC B. This is stronger than the
previous version proved only for constructed lexicographic orders. -/
theorem successorFirst_lowerPart_before_component
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e) (x : V)
    {y z : V} (hy : y ∈ O.lowerPart x)
    (hz : z ∈ O.component x) :
    OrderBefore e y z := by
  have hxy : O.StrictSuccessor x y :=
    (O.strictSuccessor_iff_mem_lowerPart x y).mpr hy
  have hxz : O.StronglyConnected x z :=
    (O.mem_component_iff x z).mp hz
  have hzy : O.StrictSuccessor z y :=
    (O.strictSuccessor_transport
      hxz (O.stronglyConnected_refl y)).mp hxy
  exact he z y hzy

/-- The lower part P_B is an initial segment of the actual order
restricted to the successor closure C_B. It need not be an initial
segment of the order on the whole ambient vertex set. -/
theorem successorFirst_lowerPart_initial_in_closure
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e) (x : V)
    {y z : V} (hy : y ∈ O.lowerPart x)
    (hz : z ∈ O.componentClosure x)
    (hzy : OrderBefore e z y) :
    z ∈ O.lowerPart x := by
  by_cases hzP : z ∈ O.lowerPart x
  · exact hzP
  have hzUnion : z ∈ O.component x ∪ O.lowerPart x := by
    rw [O.component_union_lowerPart x]
    exact hz
  have hzB : z ∈ O.component x := by
    rcases Finset.mem_union.mp hzUnion with hB | hP
    · exact hB
    · exact (hzP hP).elim
  have hyz : OrderBefore e y z :=
    O.successorFirst_lowerPart_before_component e he x hy hzB
  exact (False.elim (lt_asymm hyz hzy))

/-- A labelled vertex order, encoded by its intrinsic SCC ranking
and the comparisons made inside a single SCC. The second coordinate
is deliberately false on pairs from distinct SCCs. -/
noncomputable def globalComponentOrderSignature
    {n : ℕ} (e : Fin n ≃ V) :
    O.ComponentRanking × (V → V → Prop) :=
  (O.rankingFromEnumeration e,
    fun x y => O.StronglyConnected x y ∧ OrderBefore e x y)

/-- The component ranking in a successor-first signature is a legal
linear extension of the intrinsic component dependency order. -/
theorem globalComponentOrderSignature_legal
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e) :
    O.IsLinearComponentRanking (O.globalComponentOrderSignature e).1 :=
  O.rankingFromEnumeration_isLegal e he

/-- Two genuine interval orders with the same component signature
are literally the same enumeration of the labelled vertex set.
Without the interval hypothesis this is false. -/
theorem enumeration_eq_of_same_globalComponentOrderSignature
    {n : ℕ} (e f : Fin n ≃ V)
    (he : O.IsComponentIntervalEnumeration e)
    (hf : O.IsComponentIntervalEnumeration f)
    (hSignature :
      O.globalComponentOrderSignature e =
        O.globalComponentOrderSignature f) :
    e = f := by
  have hRank :
      O.rankingFromEnumeration e = O.rankingFromEnumeration f := by
    simpa only [globalComponentOrderSignature] using
      (congrArg Prod.fst hSignature)
  have hLocal :
      (fun x y => O.StronglyConnected x y ∧ OrderBefore e x y) =
        (fun x y => O.StronglyConnected x y ∧ OrderBefore f x y) := by
    simpa only [globalComponentOrderSignature] using
      (congrArg Prod.snd hSignature)
  apply O.enumeration_eq_of_same_component_order_and_local_orders
    e f he hf
  · intro B C
    calc
      O.firstComponentPosition e B < O.firstComponentPosition e C ↔
          O.rankingFromEnumeration e B <
            O.rankingFromEnumeration e C :=
        (O.rankingFromEnumeration_lt_iff_firstPosition e B C).symm
      _ ↔ O.rankingFromEnumeration f B <
          O.rankingFromEnumeration f C := by rw [hRank]
      _ ↔ O.firstComponentPosition f B <
          O.firstComponentPosition f C :=
        O.rankingFromEnumeration_lt_iff_firstPosition f B C
  · intro x y hsc
    have hxy :
        (O.StronglyConnected x y ∧ OrderBefore e x y) =
        (O.StronglyConnected x y ∧ OrderBefore f x y) :=
      congrFun (congrFun hLocal x) y
    change OrderBefore e x y ↔ OrderBefore f x y
    constructor
    · intro h
      have hp : O.StronglyConnected x y ∧ OrderBefore e x y :=
        ⟨hsc, h⟩
      rw [hxy] at hp
      exact hp.2
    · intro h
      have hp : O.StronglyConnected x y ∧ OrderBefore f x y :=
        ⟨hsc, h⟩
      rw [← hxy] at hp
      exact hp.2

/-- More concretely, the SCC ranking together with the inherited
orders on all one-component closures C_B determines the global
component-interval order. We only need comparisons within the
components, but this version matches the canonical local coding. -/
theorem enumeration_eq_of_same_ranking_and_closure_orders
    {n : ℕ} (e f : Fin n ≃ V)
    (he : O.IsComponentIntervalEnumeration e)
    (hf : O.IsComponentIntervalEnumeration f)
    (hRanks :
      O.rankingFromEnumeration e = O.rankingFromEnumeration f)
    (hClosure :
      ∀ x y z : V,
        y ∈ O.componentClosure x →
        z ∈ O.componentClosure x →
        (OrderBefore e y z ↔ OrderBefore f y z)) :
    e = f := by
  apply O.enumeration_eq_of_same_globalComponentOrderSignature
    e f he hf
  apply Prod.ext
  · exact hRanks
  · funext x y
    apply propext
    by_cases hsc : O.StronglyConnected x y
    · have hx : x ∈ O.componentClosure x :=
        O.component_subset_componentClosure x (O.self_mem_component x)
      have hy : y ∈ O.componentClosure x :=
        O.component_subset_componentClosure x
          ((O.mem_component_iff x y).mpr hsc)
      have hxy := hClosure x x y hx hy
      simpa [globalComponentOrderSignature, hsc] using hxy
    · simp [globalComponentOrderSignature, hsc]

/-- All genuine enumerations with whole SCCs as intervals, without
yet imposing any local adjacency-code rule. -/
noncomputable def componentIntervalEnumerations {n : ℕ} :
    Finset (Fin n ≃ V) := by
  classical
  exact Finset.univ.filter O.IsComponentIntervalEnumeration

theorem mem_componentIntervalEnumerations {n : ℕ}
    (e : Fin n ≃ V) :
    e ∈ O.componentIntervalEnumerations ↔
      O.IsComponentIntervalEnumeration e := by
  classical
  simp [componentIntervalEnumerations]

/-- The signature map is injective on the actual interval
enumerations. In particular this counts labelled vertex orders,
not an isomorphism-class quotient. -/
theorem componentIntervalOrderSignature_card {n : ℕ} :
    ((O.componentIntervalEnumerations (n := n)).image
      O.globalComponentOrderSignature).card =
    (O.componentIntervalEnumerations (n := n)).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro e he f hf hSignature
  exact O.enumeration_eq_of_same_globalComponentOrderSignature
    e f
    ((O.mem_componentIntervalEnumerations e).mp he)
    ((O.mem_componentIntervalEnumerations f).mp hf)
    hSignature

/-- Successor-first component-interval enumerations are a
subfamily of the preceding finite family. -/
noncomputable def successorFirstIntervalEnumerations {n : ℕ} :
    Finset (Fin n ≃ V) := by
  classical
  exact Finset.univ.filter (fun e =>
    O.IsComponentIntervalEnumeration e ∧
      O.IsSuccessorFirstEnumeration e)

theorem mem_successorFirstIntervalEnumerations {n : ℕ}
    (e : Fin n ≃ V) :
    e ∈ O.successorFirstIntervalEnumerations ↔
      O.IsComponentIntervalEnumeration e ∧
        O.IsSuccessorFirstEnumeration e := by
  classical
  simp [successorFirstIntervalEnumerations]

theorem successorFirstIntervalOrderSignature_card {n : ℕ} :
    ((O.successorFirstIntervalEnumerations (n := n)).image
      O.globalComponentOrderSignature).card =
    (O.successorFirstIntervalEnumerations (n := n)).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro e he f hf hSignature
  exact O.enumeration_eq_of_same_globalComponentOrderSignature
    e f
    ((O.mem_successorFirstIntervalEnumerations e).mp he).1
    ((O.mem_successorFirstIntervalEnumerations f).mp hf).1
    hSignature

end FiniteOrientation
end BigHrushovski
