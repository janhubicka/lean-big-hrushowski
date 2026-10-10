import BigHrushovski.FreshNatLabels

/-!
# Finite graph stages on a fixed natural-number carrier

A finite graph K with an injective vertex labelling into ℕ has a
transported graph relation on ℕ supported on exactly the image of
the finite vertex set. This relation agrees with K on the image.

Combined with FreshNatLabels, any finite strong extension A ≤ B
can be represented on a new finite subset of ℕ, retaining the
labels of A and adding only fresh labels for the other vertices.
The old finite labelled graph is an induced strong subgraph of
the new finite stage.

This is the local *carrier and graph transport* step. Realizing
the fair catalogue and taking a coherent countable union remain
separate proof obligations.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*}

/-- A graph on ℕ supported on the image of a graph embedding. -/
def transportedToNat (K : GraphOn V)
    (label : V → ℕ) (hLabel : Function.Injective label) : GraphOn ℕ where
  adj x y :=
    ∃ u v : V, label u = x ∧ label v = y ∧ K.adj u v
  symm := by
    intro x y h
    obtain ⟨u, v, hu, hv, hadj⟩ := h
    exact ⟨v, u, hv, hu, K.symm u v hadj⟩
  irrefl := by
    intro x h
    obtain ⟨u, v, hu, hv, hadj⟩ := h
    have huv : u = v := hLabel (hu.trans hv.symm)
    subst v
    exact K.irrefl u hadj

/-- The graph induced on the labelled vertices is exactly K,
including its nonedges. -/
theorem transportedToNat_induced
    (K : GraphOn V) (label : V → ℕ)
    (hLabel : Function.Injective label) (u v : V) :
    K.adj u v ↔ (K.transportedToNat label hLabel).adj (label u) (label v) := by
  constructor
  · intro h
    exact ⟨u, v, rfl, rfl, h⟩
  · rintro ⟨u', v', hu, hv, hadj⟩
    have huu : u' = u := hLabel hu
    have hvv : v' = v := hLabel hv
    subst u'
    subst v'
    exact hadj

/-- No edges lie outside the finite labelled domain. -/
theorem transportedToNat_support
    [Fintype V] [DecidableEq V]
    (K : GraphOn V) (label : V → ℕ)
    (hLabel : Function.Injective label)
    {x y : ℕ}
    (h : (K.transportedToNat label hLabel).adj x y) :
    x ∈ (Finset.univ : Finset V).image label ∧
      y ∈ (Finset.univ : Finset V).image label := by
  obtain ⟨u, v, hu, hv, _⟩ := h
  exact ⟨Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩,
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩⟩

/-- Predimension is exactly preserved in the natural-number presentation. -/
theorem transportedToNat_predim
    [DecidableEq V]
    (K : GraphOn V) (label : V → ℕ)
    (hLabel : Function.Injective label) (s : Finset V) :
    (K.transportedToNat label hLabel).predim (s.image label) =
      K.predim s := by
  exact K.predim_image (K.transportedToNat label hLabel)
    label hLabel (fun x y => K.transportedToNat_induced label hLabel x y) s

/-- Two-sparsity transfers to the finite image inside ℕ. -/
theorem transportedToNat_sparse
    [DecidableEq V]
    (K : GraphOn V) (label : V → ℕ)
    (hLabel : Function.Injective label)
    {s : Finset V} (hSparse : K.IsTwoSparse s) :
    (K.transportedToNat label hLabel).IsTwoSparse (s.image label) :=
  (K.twoSparse_image_iff (K.transportedToNat label hLabel)
    label hLabel
    (fun x y => K.transportedToNat_induced label hLabel x y)
    s).mpr hSparse

/-- Relative strongness transfers to an induced labelled subgraph. -/
theorem transportedToNat_strong
    [DecidableEq V]
    (K : GraphOn V) (label : V → ℕ)
    (hLabel : Function.Injective label)
    {a b : Finset V}
    (hab : K.toPredimension.IsStrong a b) :
    (K.transportedToNat label hLabel).toPredimension.IsStrong
      (a.image label) (b.image label) :=
  (K.strong_image_iff (K.transportedToNat label hLabel)
    label hLabel
    (fun x y => K.transportedToNat_induced label hLabel x y)
    a b hab.1).mpr hab


/-- When a finite induced graph extension is re-labelled over the old
natural-number labels, the previous graph and the new graph agree on
every pair of old vertices. This is the coherence invariant needed to
form the countable union of finite graph stages. -/
theorem transportedToNat_agree_on_old
    {A B : Type*}
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : GraphOn A) (K : GraphOn B)
    (i : A → B) (hi : Function.Injective i)
    (hInduced : ∀ a b : A,
      G.adj a b ↔ K.adj (i a) (i b))
    (old : A → ℕ) (hOld : Function.Injective old)
    {x y : ℕ}
    (hx : x ∈ (Finset.univ : Finset A).image old)
    (hy : y ∈ (Finset.univ : Finset A).image old) :
    (G.transportedToNat old hOld).adj x y ↔
      (K.transportedToNat (FiniteSpan.extendNatLabels i old)
        (FiniteSpan.extendNatLabels_injective i hi old hOld)).adj x y := by
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
  subst x
  subst y
  have hOldAdj := G.transportedToNat_induced old hOld a b
  have hNewAdj :=
    K.transportedToNat_induced
      (FiniteSpan.extendNatLabels i old)
      (FiniteSpan.extendNatLabels_injective i hi old hOld)
      (i a) (i b)
  have hNewAdj' : K.adj (i a) (i b) ↔
      (K.transportedToNat (FiniteSpan.extendNatLabels i old)
        (FiniteSpan.extendNatLabels_injective i hi old hOld)).adj
          (old a) (old b) := by
    simpa only [FiniteSpan.extendNatLabels_comp i hi old a,
      FiniteSpan.extendNatLabels_comp i hi old b] using hNewAdj
  exact hOldAdj.symm.trans ((hInduced a b).trans hNewAdj')

end GraphOn

namespace FiniteSpan

/-- Realize a finite strong extension on a fixed Nat carrier, fixing
every old vertex label and using fresh labels for every new vertex.
The transported graph has support on precisely this finite stage. -/
theorem exists_fresh_strong_nat_stage
    {A B : Type*}
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (K : GraphOn B)
    (i : A → B) (hi : Function.Injective i)
    (hStrong : K.toPredimension.IsStrong
      ((Finset.univ : Finset A).image i)
      (Finset.univ : Finset B))
    (hSparse : K.IsTwoSparse (Finset.univ : Finset B))
    (old : A → ℕ) (hOld : Function.Injective old) :
    ∃ (new : B → ℕ) (N : GraphOn ℕ),
      Function.Injective new ∧
      (∀ a : A, new (i a) = old a) ∧
      (∀ b c : B, K.adj b c ↔ N.adj (new b) (new c)) ∧
      N.IsTwoSparse ((Finset.univ : Finset B).image new) ∧
      N.toPredimension.IsStrong
        ((Finset.univ : Finset A).image old)
        ((Finset.univ : Finset B).image new) ∧
      (∀ x y : ℕ, N.adj x y →
        x ∈ (Finset.univ : Finset B).image new ∧
        y ∈ (Finset.univ : Finset B).image new) := by
  classical
  let new : B → ℕ := extendNatLabels i old
  have hNew : Function.Injective new :=
    extendNatLabels_injective i hi old hOld
  let N : GraphOn ℕ := K.transportedToNat new hNew
  have hSparseN : N.IsTwoSparse
      ((Finset.univ : Finset B).image new) :=
    K.transportedToNat_sparse new hNew hSparse
  have hStrongN : N.toPredimension.IsStrong
      (((Finset.univ : Finset A).image i).image new)
      ((Finset.univ : Finset B).image new) :=
    K.transportedToNat_strong new hNew hStrong
  have hOldImage :
      (((Finset.univ : Finset A).image i).image new) =
      ((Finset.univ : Finset A).image old) := by
    calc
      _ = (Finset.univ : Finset A).image (new ∘ i) := by
            rw [Finset.image_image]
      _ = (Finset.univ : Finset A).image old := by
            congr 1
            funext a
            exact extendNatLabels_comp i hi old a
  rw [hOldImage] at hStrongN
  refine ⟨new, N, hNew, ?_, ?_, hSparseN, hStrongN, ?_⟩
  · intro a
    exact extendNatLabels_comp i hi old a
  · intro b c
    exact K.transportedToNat_induced new hNew b c
  · intro x y h
    exact K.transportedToNat_support new hNew h

end FiniteSpan
end BigHrushovski
