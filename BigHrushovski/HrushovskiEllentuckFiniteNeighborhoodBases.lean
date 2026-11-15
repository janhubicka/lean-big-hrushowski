import BigHrushovski.HrushovskiEllentuckFiniteCutTopology
import RamseySpace.Examples.SupportedEllentuck

/-!
# Finite observation bases of the actual C_F complete-support domains

The Cantor-product (finite vertex membership observation) topology
on the family of actual complete-support domains U[S] agrees with
the finite-approximation *metric* topology of their increasing
birth-level enumerations. This is proved through two explicit,
cofinal systems of finite observations; no topological equality
is postulated as an axiom.

The finer Ellentuck topology, whose basic neighborhoods also
require refinement of an infinite copy, is NOT identified with
the product topology. The comparison here concerns only the
finite-approximation metric topology.

The theorem is independent of the actual ordered R/H copy-domain
equivalence and therefore can be checked against the already
merged supported-domain, finite-cut sources.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- A strictly increasing enumeration has at least n as its
nth value. Thus a number below m, when enumerated, must
occur at one of the first m positions. -/
theorem increasingPoint_index_le_value
    (X : RamseySpace.Examples.Ellentuck.Point) (n : ℕ) :
    n ≤ X n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hlt : X n < X (n + 1) :=
      X.strictMono (Nat.lt_succ_self n)
    omega

/-- Equality of the first m entries of two increasing
enumerations forces equality of their membership observations
at *all* levels below m. -/
theorem increasingPoint_level_agree_of_prefix
    (X Y : RamseySpace.Examples.Ellentuck.Point) (m : ℕ)
    (hPrefix : ∀ i : ℕ, i < m → X i = Y i) :
    ∀ q : ℕ, q < m →
      (q ∈ Set.range X ↔ q ∈ Set.range Y) := by
  intro q hq
  constructor
  · rintro ⟨i, hi⟩
    have him : i < m := by
      have hle := increasingPoint_index_le_value X i
      omega
    exact ⟨i, (hPrefix i him).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    have him : i < m := by
      have hle := increasingPoint_index_le_value Y i
      omega
    exact ⟨i, (hPrefix i him).trans hi⟩

/-- Converse at a *point-dependent* finite cutoff.
If two infinite level sets agree below X(n)+1, their unique
increasing enumerations agree through position n.

The cutoff depends on X: no uniform finite level cutoff can
recover an arbitrary fixed number of selected levels when
the enumerations may have arbitrarily large gaps. -/
theorem increasingPoint_prefix_of_level_agree
    (X Y : RamseySpace.Examples.Ellentuck.Point) (n : ℕ)
    (hBelow : ∀ q : ℕ, q < X n + 1 →
      (q ∈ Set.range X ↔ q ∈ Set.range Y)) :
    ∀ i : ℕ, i ≤ n → X i = Y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hXi : X i < X n + 1 := by
      have hMon : X i ≤ X n := X.monotone hi
      omega
    have hNotXY : ¬ X i < Y i := by
      intro hXY
      have hMem : X i ∈ Set.range Y :=
        (hBelow (X i) hXi).mp ⟨i, rfl⟩
      obtain ⟨j, hYj⟩ := hMem
      have hji : j < i := by
        by_contra hnot
        have hij : i ≤ j := by omega
        have hYij : Y i ≤ Y j := Y.monotone hij
        omega
      have hInd : X j = Y j := ih j hji (by omega)
      have hEq : X j = X i := hInd.trans hYj
      have hSame : j = i := X.injective hEq
      omega
    have hNotYX : ¬ Y i < X i := by
      intro hYX
      have hYi : Y i < X n + 1 := by omega
      have hMem : Y i ∈ Set.range X :=
        (hBelow (Y i) hYi).mpr ⟨i, rfl⟩
      obtain ⟨j, hXj⟩ := hMem
      have hji : j < i := by
        by_contra hnot
        have hij : i ≤ j := by omega
        have hXij : X i ≤ X j := X.monotone hij
        omega
      have hInd : X j = Y j := ih j hji (by omega)
      have hEq : Y j = Y i := hInd.symm.trans hXj
      have hSame : j = i := Y.injective hEq
      omega
    omega

/-- Every finite vertex-stage observation of the full
generated-support domains follows from a sufficiently long
(common, fixed-length) approximation prefix. -/
theorem supportedStage_agree_of_increasingPrefix
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (X Y : RamseySpace.Examples.Ellentuck.Point) (m : ℕ)
    (hPrefix : ∀ i : ℕ, i < m → X i = Y i) :
    ∀ v : Vertex F K, v ∈ stageImage F K m →
      (v ∈ birthLevelDomain F K (Set.range X) ↔
        v ∈ birthLevelDomain F K (Set.range Y)) :=
  (birthLevelDomain_agree_on_stage_iff F K hReq
    (Set.range X) (Set.range Y) m).mp
    (increasingPoint_level_agree_of_prefix X Y m hPrefix)

/-- Conversely, for any fixed infinite copy X and any
approximation length n+1, agreement of the *actual vertex
domains* through birth stage X(n)+1 forces agreement of
the increasing enumerations through index n. -/
theorem increasingPrefix_agree_of_supportedStage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (X Y : RamseySpace.Examples.Ellentuck.Point) (n : ℕ)
    (hStage : ∀ v : Vertex F K,
      v ∈ stageImage F K (X n + 1) →
        (v ∈ birthLevelDomain F K (Set.range X) ↔
          v ∈ birthLevelDomain F K (Set.range Y))) :
    ∀ i : ℕ, i ≤ n → X i = Y i := by
  apply increasingPoint_prefix_of_level_agree X Y n
  exact (birthLevelDomain_agree_on_stage_iff F K hReq
    (Set.range X) (Set.range Y) (X n + 1)).mpr hStage

end BigHrushovski.CFCoherentTower
