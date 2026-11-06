import BigHrushovski.C0CoordinateLocalOrderChoice

/-!
# Each chronologically ordered canonical finite C₀ closure is a local representative

The previous module makes an explicit *choice of order* on a local
representative and transports it along chosen underlying bijections.
Here we show that the one-generated closure in any finite canonical
C₀ presentation with its chronological order supplies such a
representative on the LITERAL induced subtype.

Its lower part is the intrinsic set P(a)=C(a)\B(a), and its top part
is the complete component B(a), without singling out a generator
inside B. All top vertices have complete value equal to the whole
restricted carrier. This result is independent of the minimal-strong
step hypotheses (which are required only for finite-age membership).

The global catalogue choosing ONE representative order for each
unordered local type with its ordered lower part remains separate.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {n : ℕ}

/-- For any canonical finite C₀ component presentation, every edge
is covered by the complete unary closure of one of its endpoints.
This is a purely finite consequence of backward dependencies and
requires neither sparsity nor minimal-strong-step hypotheses. -/
theorem canonicalValue_edge_covered
    (G : GraphOn V) (κ : V → Fin n) (u v : V)
    (hadj : G.adj u v) :
    v ∈ FiniteC0.canonicalValue G κ u ∨
      u ∈ FiniteC0.canonicalValue G κ v := by
  rcases lt_trichotomy (κ u) (κ v) with huv | heq | hvu
  · right
    have hDep : FiniteC0.backDependency G κ (κ v) (κ u) :=
      ⟨huv, v, u, rfl, rfl, G.symm u v hadj⟩
    exact (FiniteC0.mem_canonicalValue_iff G κ v u).mpr
      (TaggedAmalgam.DependencyAncestor.step
        TaggedAmalgam.DependencyAncestor.root hDep)
  · left
    apply (FiniteC0.mem_canonicalValue_iff G κ u v).mpr
    rw [← heq]
    exact TaggedAmalgam.DependencyAncestor.root
  · left
    have hDep : FiniteC0.backDependency G κ (κ u) (κ v) :=
      ⟨hvu, u, v, rfl, rfl, hadj⟩
    exact (FiniteC0.mem_canonicalValue_iff G κ u v).mpr
      (TaggedAmalgam.DependencyAncestor.step
        TaggedAmalgam.DependencyAncestor.root hDep)

/-- The intrinsic lower closure of a as a literal subset of its
finite one-generated unary closure. -/
noncomputable def canonicalLocalLower
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    Finset (FiniteC0.canonicalValue G κ a) :=
  Finset.univ.filter (fun b =>
    b.val ∈ unaryLowerClosure (FiniteC0.canonicalValue G κ) a)

theorem mem_canonicalLocalLower_iff
    (G : GraphOn V) (κ : V → Fin n) (a : V)
    (b : FiniteC0.canonicalValue G κ a) :
    b ∈ canonicalLocalLower G κ a ↔
      b.val ∈ unaryLowerClosure (FiniteC0.canonicalValue G κ) a := by
  classical
  simp [canonicalLocalLower]

/-- The complete induced local closure C(a), with its intrinsic lower
part and the inherited chronological order, is an explicitly chosen
local representative. The temporary generating vertex a is not a
distinguished vertex of the resulting representative. -/
noncomputable def canonicalLocalRepresentative
    (G : GraphOn V) (κ : V → Fin n)
    (hOrder : ChronologicalBlockOrder κ) (a : V) :
    LocalOrderedRepresentative
      (FiniteC0.canonicalValue G κ a) := by
  classical
  let C : V → Finset V := FiniteC0.canonicalValue G κ
  let S : Finset V := C a
  let P : Finset V := unaryLowerClosure C a
  let L : Finset S := canonicalLocalLower G κ a
  have hReflexive : ∀ b : S, b ∈ restrictValue C S b := by
    intro b
    exact (mem_restrictValue_iff C S b b).mpr
      (FiniteC0.canonicalValue_mem_self G κ b.val)
  have hNested : ∀ b c : S,
      c ∈ restrictValue C S b →
      restrictValue C S c ⊆ restrictValue C S b := by
    intro b c hbc d hcd
    have hbc' : c.val ∈ C b.val :=
      (mem_restrictValue_iff C S b c).mp hbc
    have hcd' : d.val ∈ C c.val :=
      (mem_restrictValue_iff C S c d).mp hcd
    exact (mem_restrictValue_iff C S b d).mpr
      (FiniteC0.canonicalValue_mem_trans G κ hbc' hcd')
  have hEdgeCover : ∀ b c : S,
      (restrictGraph G S).adj b c →
        c ∈ restrictValue C S b ∨
        b ∈ restrictValue C S c := by
    intro b c hadj
    have hAdjG : G.adj b.val c.val := hadj
    rcases canonicalValue_edge_covered G κ b.val c.val hAdjG with
      hbc | hcb
    · exact Or.inl ((mem_restrictValue_iff C S b c).mpr hbc)
    · exact Or.inr ((mem_restrictValue_iff C S c b).mpr hcb)
  have hClosed : ClosedUnder (restrictValue C S) L := by
    intro b hb w hw
    have hbP : b.val ∈ P :=
      (mem_canonicalLocalLower_iff G κ a b).mp hb
    have hwC : w.val ∈ C b.val :=
      (mem_restrictValue_iff C S b w).mp hw
    have hwP : w.val ∈ P :=
      canonical_unaryLowerClosure_closed G κ a b.val hbP hwC
    exact (mem_canonicalLocalLower_iff G κ a w).mpr hwP
  have hOrder' : ∀ p ∈ L, ∀ b ∉ L, p < b := by
    intro p hp b hb
    have hpP : p.val ∈ P :=
      (mem_canonicalLocalLower_iff G κ a p).mp hp
    have hbNotP : b.val ∉ P := by
      intro h
      exact hb ((mem_canonicalLocalLower_iff G κ a b).mpr h)
    have hbTop : b.val ∈ unaryComponentClass C a := by
      have hInS : b.val ∈ C a := b.property
      have hUnion : b.val ∈ P ∪ unaryComponentClass C a := by
        rw [← canonical_lower_union_component G κ a]
        exact hInS
      rcases Finset.mem_union.mp hUnion with hP | hB
      · exact (hbNotP hP).elim
      · exact hB
    exact canonical_lower_before_top G κ hOrder a hpP hbTop
  have hGenerates : ∀ b : S, b ∉ L →
      restrictValue C S b = Finset.univ := by
    intro b hb
    have hbNotP : b.val ∉ P := by
      intro h
      exact hb ((mem_canonicalLocalLower_iff G κ a b).mpr h)
    have hbTop : b.val ∈ unaryComponentClass C a := by
      have hUnion : b.val ∈ P ∪ unaryComponentClass C a := by
        rw [← canonical_lower_union_component G κ a]
        exact b.property
      rcases Finset.mem_union.mp hUnion with hP | hB
      · exact (hbNotP hP).elim
      · exact hB
    have hEq : C b.val = C a :=
      (Finset.mem_filter.mp hbTop).2
    ext w
    simp only [Finset.mem_univ, iff_true]
    exact (mem_restrictValue_iff C S b w).mpr (by
      rw [hEq]
      exact w.property)
  have hTop : (Finset.univ \ L).Nonempty := by
    let u : S :=
      ⟨a, FiniteC0.canonicalValue_mem_self G κ a⟩
    refine ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro haL
    have haP : a ∈ P :=
      (mem_canonicalLocalLower_iff G κ a u).mp haL
    have haTop : a ∈ unaryComponentClass C a :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp haP).2 haTop
  exact {
    graph := restrictGraph G S
    value := restrictValue C S
    lower := L
    value_reflexive := hReflexive
    value_nested := hNested
    graph_edge_covered := hEdgeCover
    lower_closed := hClosed
    lower_before_top := hOrder'
    top_generates := hGenerates
    top_nonempty := hTop
  }

/-- The constructed local representative has a closed lower part
and puts it entirely before the top component. This endpoint keeps
the chronological-order hypothesis explicit. -/
theorem canonicalLocalRepresentative_lower_order
    (G : GraphOn V) (κ : V → Fin n)
    (hOrder : ChronologicalBlockOrder κ) (a : V)
    {p b : FiniteC0.canonicalValue G κ a}
    (hp : p ∈ (canonicalLocalRepresentative G κ hOrder a).lower)
    (hb : b ∉ (canonicalLocalRepresentative G κ hOrder a).lower) :
    p < b :=
  (canonicalLocalRepresentative G κ hOrder a).lower_before_top
    p hp b hb

end FiniteUnaryCoordinates
end BigHrushovski
