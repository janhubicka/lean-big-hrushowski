import BigHrushovski.GenericStrongClosure

/-!
# Strict predimension minimality of finite strong closures

In the finite strong closure C of X, every proper intermediate
set D with X ⊆ D ⊊ C has strictly greater predimension than C.

This observation is used in the manuscript's argument that the
finite induced diagram of C over X has no competing realization
outside C. We first prove the abstract finite-minimizer lemma for
an arbitrary submodular predimension, and then specialize to the
concrete countable strong Hrushovski generic.

No model-theoretic algebraic closure is asserted here. That
identification requires a further argument about definable finite
diagrams and infinitely many conjugates.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- In every finite ambient set c, there is an extension b of a
minimizing predimension among all subsets between a and c.
Every such minimizer is strong in c. -/
theorem exists_min_delta_strong
    (d : Predimension V) (a c : Finset V) (hac : a ⊆ c) :
    ∃ b : Finset V, a ⊆ b ∧ d.IsStrong b c ∧
      ∀ t : Finset V, a ⊆ t → t ⊆ c → d.delta b ≤ d.delta t := by
  classical
  let family : Finset (Finset V) :=
    c.powerset.filter (fun t => a ⊆ t)
  have hcFamily : c ∈ family := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (by intro v hv; exact hv), hac⟩
  let values : Finset ℤ := family.image d.delta
  have hNonempty : values.Nonempty := by
    refine ⟨d.delta c, ?_⟩
    exact Finset.mem_image.mpr ⟨c, hcFamily, rfl⟩
  obtain ⟨b, hb, hmin⟩ :=
    Finset.mem_image.mp (Finset.min'_mem values hNonempty)
  have hab : a ⊆ b :=
    (Finset.mem_filter.mp hb).2
  have hbc : b ⊆ c :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
  have hMinimum (t : Finset V) (hat : a ⊆ t) (htc : t ⊆ c) :
      d.delta b ≤ d.delta t := by
    rw [hmin]
    apply Finset.min'_le values (d.delta t)
    exact Finset.mem_image.mpr
      ⟨t, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr htc, hat⟩, rfl⟩
  refine ⟨b, hab, ⟨hbc, ?_⟩, hMinimum⟩
  intro t hbt htc
  exact hMinimum t (hab.trans hbt) htc

/-- If c is the least globally strong finite set containing a,
every proper intermediate set containing a has strictly larger δ. -/
theorem strict_delta_of_least_global
    (d : Predimension V) (a c : Finset V)
    (hac : a ⊆ c)
    (hc : d.IsGloballyStrong c)
    (hLeast : ∀ b : Finset V,
      d.IsGloballyStrong b → a ⊆ b → c ⊆ b)
    (t : Finset V) (hat : a ⊆ t) (htc : t ⊆ c)
    (htne : t ≠ c) :
    d.delta c < d.delta t := by
  obtain ⟨b, hab, hbc, hMinimum⟩ :=
    d.exists_min_delta_strong a c hac
  have hbGlobal : d.IsGloballyStrong b :=
    d.globallyStrong_of_strong_in_global hbc hc
  have hbcEq : b = c :=
    le_antisymm hbc.1 (hLeast b hbGlobal hab)
  have hAll (u : Finset V) (hau : a ⊆ u) (huc : u ⊆ c) :
      d.delta c ≤ d.delta u := by
    rw [← hbcEq]
    exact hMinimum u hau huc
  have hBound : d.delta c ≤ d.delta t := hAll t hat htc
  by_contra hNotStrict
  have hEqual : d.delta c = d.delta t := by omega
  have htStrong : d.IsStrong t c := by
    refine ⟨htc, ?_⟩
    intro u htu huc
    have hLower := hAll u (hat.trans htu) huc
    omega
  have htGlobal : d.IsGloballyStrong t :=
    d.globallyStrong_of_strong_in_global htStrong hc
  exact htne (le_antisymm htc (hLeast t htGlobal hat))

/-- A finite set b of the same predimension as a closed c and
containing its generators must also contain c.
This needs no cardinality assumption on b. -/
theorem closed_subset_of_equal_delta
    (d : Predimension V) (a c b : Finset V)
    (hac : a ⊆ c)
    (hc : d.IsGloballyStrong c)
    (hStrict : ∀ t : Finset V, a ⊆ t → t ⊆ c →
      t ≠ c → d.delta c < d.delta t)
    (hab : a ⊆ b)
    (hDelta : d.delta b = d.delta c) :
    c ⊆ b := by
  by_contra hNotSubset
  have hMeetNe : c ∩ b ≠ c := by
    intro hEq
    apply hNotSubset
    intro v hv
    have hMem : v ∈ c ∩ b := by rw [hEq]; exact hv
    exact (Finset.mem_inter.mp hMem).2
  have haMeet : a ⊆ c ∩ b := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hac hv, hab hv⟩
  have hStrictMeet :=
    hStrict (c ∩ b) haMeet Finset.inter_subset_left hMeetNe
  have hStrongUnion := hc (c ∪ b) Finset.subset_union_left
  have hUnion : d.delta c ≤ d.delta (c ∪ b) :=
    hStrongUnion.2 (c ∪ b) Finset.subset_union_left
      (by intro v hv; exact hv)
  have hSub := d.submodular c b
  rw [hDelta] at hSub
  omega

end Predimension

namespace FiniteCatalogue

/-- The least globally strong finite closure has strictly smaller
predimension than every proper intermediate superset of its generators. -/
theorem genericStrongClosure_strict_delta
    (s t : Finset ℕ)
    (hst : s ⊆ t)
    (htc : t ⊆ genericStrongClosure s)
    (htne : t ≠ genericStrongClosure s) :
    genericTwoSparseGraph.predim (genericStrongClosure s) <
      genericTwoSparseGraph.predim t := by
  exact (genericTwoSparseGraph.toPredimension).strict_delta_of_least_global
    s (genericStrongClosure s)
    (subset_genericStrongClosure s)
    (genericStrongClosure_global s)
    (fun b hb hsb => genericStrongClosure_least s b hb hsb)
    t hst htc htne

/-- Predimension equality over the generators forces containment
of their entire strong closure, even if the competing set is larger. -/
theorem genericStrongClosure_subset_of_equal_delta
    (s b : Finset ℕ) (hsb : s ⊆ b)
    (hDelta : genericTwoSparseGraph.predim b =
      genericTwoSparseGraph.predim (genericStrongClosure s)) :
    genericStrongClosure s ⊆ b := by
  exact (genericTwoSparseGraph.toPredimension).closed_subset_of_equal_delta
    s (genericStrongClosure s) b
    (subset_genericStrongClosure s)
    (genericStrongClosure_global s)
    (fun t hst htc htne =>
      genericStrongClosure_strict_delta s t hst htc htne)
    hsb hDelta

/-- A competing finite induced diagram over the generators cannot
occupy a different finite set when its cardinality and predimension
agree with those of the strong closure. -/
theorem genericStrongClosure_unique_equal_pattern
    (s b : Finset ℕ) (hsb : s ⊆ b)
    (hCard : b.card = (genericStrongClosure s).card)
    (hDelta : genericTwoSparseGraph.predim b =
      genericTwoSparseGraph.predim (genericStrongClosure s)) :
    b = genericStrongClosure s := by
  have hSubset := genericStrongClosure_subset_of_equal_delta s b hsb hDelta
  have hEq : genericStrongClosure s = b :=
    Finset.eq_of_subset_of_card_le hSubset (by omega)
  exact hEq.symm

end FiniteCatalogue
end BigHrushovski
