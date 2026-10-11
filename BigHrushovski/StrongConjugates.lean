import BigHrushovski.UnboundedStrongCopies
import BigHrushovski.StrongHomogeneity
import BigHrushovski.FiniteImageEquiv

/-!
# Arbitrarily many conjugates of vertices outside a strong closure

Given a finite globally strong C in the constructed countable generic
and a vertex a outside C, every finite forbidden set F can be avoided
by an automorphism fixing C pointwise: there is an induced automorphism
e of the whole graph with e(a) outside F.

Take D to be the finite globally strong closure of C ∪ {a}.
The finite-copy avoidance theorem gives a globally strong induced
copy of D over C whose new vertices miss F. By strong homogeneity,
the induced partial isomorphism D → image(D) extends to a global
automorphism of the generic. In particular, the pointwise
stabilizer of C has an infinite orbit on a.

This is the combinatorial conjugacy half of proving
acl(X) ⊆ cl_s(X). A first-order definition and its invariance
under automorphisms are treated separately.
-/

namespace BigHrushovski
namespace FiniteCatalogue

private theorem subtype_univ_to_finset (s : Finset ℕ) :
    (Finset.univ : Finset {v : ℕ // v ∈ s}).image Subtype.val = s := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact v.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A vertex outside any finite globally strong base can be moved
outside an arbitrarily prescribed finite forbidden set by an
automorphism fixing that base pointwise. -/
theorem generic_strong_automorphism_avoids
    (c : Finset ℕ)
    (hc : genericTwoSparseGraph.toPredimension.IsGloballyStrong c)
    (a : ℕ) (ha : a ∉ c)
    (forbidden : Finset ℕ) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        genericTwoSparseGraph.adj x y ↔
          genericTwoSparseGraph.adj (e x) (e y)) ∧
      (∀ x ∈ c, e x = x) ∧
      e a ∉ forbidden := by
  classical
  let d := genericStrongClosure (insert a c)
  have hInsD : insert a c ⊆ d :=
    subset_genericStrongClosure (insert a c)
  have hCD : c ⊆ d := by
    intro x hx
    exact hInsD (Finset.mem_insert_of_mem hx)
  have haD : a ∈ d :=
    hInsD (Finset.mem_insert_self a c)
  have hGlobalD :
      genericTwoSparseGraph.toPredimension.IsGloballyStrong d :=
    genericStrongClosure_global (insert a c)
  let P := {v : ℕ // v ∈ c}
  let D := {v : ℕ // v ∈ d}
  let H : GraphOn D :=
    genericTwoSparseGraph.pullback (Subtype.val : D → ℕ)
  let j : P → D := fun p => ⟨p.val, hCD p.property⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (Subtype.val : D → ℕ) hxy
  have hInducedJ : ∀ p q : P,
      H.adj (j p) (j q) ↔
        genericTwoSparseGraph.adj p.val q.val :=
    fun _ _ => Iff.rfl
  have hSparseD : H.IsTwoSparse (Finset.univ : Finset D) := by
    have h := H.twoSparse_image_iff genericTwoSparseGraph
      (Subtype.val : D → ℕ)
      Subtype.val_injective (fun _ _ => Iff.rfl)
      (Finset.univ : Finset D)
    rw [subtype_univ_to_finset d] at h
    exact h.mp (by intro s _; exact genericTwoSparseGraph_sparse s)
  have hImageJ :
      (((Finset.univ : Finset P).image j).image
        (Subtype.val : D → ℕ)) = c := by
    rw [Finset.image_image]
    have hComp :
        (Subtype.val : D → ℕ) ∘ j =
          (Subtype.val : P → ℕ) := by
      funext p
      rfl
    rw [hComp]
    exact subtype_univ_to_finset c
  have hStrongJD : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j)
      (Finset.univ : Finset D) := by
    have h := (H.strong_image_iff genericTwoSparseGraph
      (Subtype.val : D → ℕ)
      Subtype.val_injective (fun _ _ => Iff.rfl)
      ((Finset.univ : Finset P).image j)
      (Finset.univ : Finset D)
      (Finset.subset_univ _)).mp (by
        rw [hImageJ, subtype_univ_to_finset d]
        exact hc d hCD)
    exact h
  obtain ⟨g, hg, hAdjG, hFixC, hGlobalG, hAvoid⟩ :=
    generic_exists_strong_copy_avoiding
      c forbidden hc H j hj hInducedJ hSparseD hStrongJD
  let pIso : FiniteStrongPartialIso
      genericTwoSparseGraph genericTwoSparseGraph :=
    { source := d
      target := (Finset.univ : Finset D).image g
      equiv := FiniteSpan.finiteImageEquiv g hg
      source_global := hGlobalD
      target_global := hGlobalG
      induced := by
        intro x y
        exact hAdjG x y }
  obtain ⟨e, hIndE, hExtE⟩ :=
    genericTwoSparseGraph_strongHomogeneous pIso
  have hFix : ∀ x ∈ c, e x = x := by
    intro x hx
    let px : P := ⟨x, hx⟩
    have hxd : x ∈ d := hCD hx
    calc
      e x = (pIso.equiv ⟨x, hxd⟩).val := hExtE ⟨x, hxd⟩
      _ = g (j px) := rfl
      _ = x := hFixC px
  have hEa : e a = g ⟨a, haD⟩ :=
    hExtE ⟨a, haD⟩
  have hNotF : e a ∉ forbidden := by
    intro hEF
    rw [hEa] at hEF
    obtain ⟨p, hp⟩ := hAvoid ⟨a, haD⟩ hEF
    have hEq : a = p.val := congrArg Subtype.val hp
    apply ha
    rw [hEq]
    exact p.property
  exact ⟨e, hIndE, hFix, hNotF⟩

/-- Outside a finite strong closure, the pointwise stabilizer of
its finite generators moves the vertex outside every finite set. -/
theorem generic_outside_closure_infinite_orbit
    (s : Finset ℕ) (a : ℕ)
    (ha : a ∉ genericStrongClosure s)
    (forbidden : Finset ℕ) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        genericTwoSparseGraph.adj x y ↔
          genericTwoSparseGraph.adj (e x) (e y)) ∧
      (∀ x ∈ s, e x = x) ∧
      e a ∉ forbidden := by
  obtain ⟨e, hInd, hFix, hAvoid⟩ :=
    generic_strong_automorphism_avoids
      (genericStrongClosure s) (genericStrongClosure_global s)
      a ha forbidden
  refine ⟨e, hInd, ?_, hAvoid⟩
  intro x hx
  exact hFix x (subset_genericStrongClosure s hx)

/-- Every finite set invariant under all automorphisms fixing s
is contained in the finite strong closure of s. In particular,
this applies to the finite solution set of any algebraic formula
over s, once first-order formula semantics are provided. -/
theorem generic_invariant_finite_subset_strongClosure
    (s f : Finset ℕ)
    (hInvariant : ∀ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        genericTwoSparseGraph.adj x y ↔
          genericTwoSparseGraph.adj (e x) (e y)) →
      (∀ x ∈ s, e x = x) →
      ∀ a ∈ f, e a ∈ f) :
    f ⊆ genericStrongClosure s := by
  intro a haf
  by_contra haOutside
  obtain ⟨e, hInd, hFix, hAvoid⟩ :=
    generic_outside_closure_infinite_orbit s a haOutside f
  exact hAvoid (hInvariant e hInd hFix a haf)

end FiniteCatalogue
end BigHrushovski
