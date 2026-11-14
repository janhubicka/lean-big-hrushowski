import BigHrushovski.C0CoordinateFiniteStageSparsity
import BigHrushovski.C0CoordinateRawClosedOverlap
import BigHrushovski.C0FiniteCanonicalValues

/-!
# Strongness of complete-unary closed overlaps in finite raw C₀ witnesses

The existing finite two-sided functional amalgamation theorem does
not require numerical agreement of component ranks on the common
base. It requires each factor to have genuine finite canonical
stages, its full named C-values on the base, and 2-sparseness.

For any finite canonical stage/value witness (empty steps allowed),
every subset closed under the COMPLETE C-function is strong in
the whole finite graph. We reuse the already proved finite C₀
closed-strong lemma.

Applied to two finitely presented raw-host subsets S,T, their
literal intersection is strong in both factors. This discharges
the strong-base property for the forthcoming free amalgamation
of two complete raw-host closed finite structures. It does not
yet construct that amalgam or prove the converse finite age.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A subset closed under all COMPLETE named unary C-values is
strong in every finite graph equipped with canonical C₀ stage/value
data. The proof allows empty stages and never assumes a separate
strongness axiom for the base. -/
theorem hasCanonicalC0StageValues_closed_strong
    (G : GraphOn U) (C : U → Finset U)
    (h : HasCanonicalC0StageValues G C)
    (s : Finset U) (hClosed : ∀ u ∈ s, C u ⊆ s) :
    G.toPredimension.IsStrong s Finset.univ := by
  classical
  obtain ⟨n,κ,hSteps,hValues⟩ := h
  have hStrongSteps : ∀ k : ℕ, k < n →
      G.toPredimension.IsStrong
        (FiniteC0.oldStage κ k)
        (FiniteC0.oldStage κ (k+1)) := by
    intro k hk
    rcases hSteps k hk with hEq | hMin
    · rw [hEq]
      exact G.toPredimension.strong_refl _
    · exact hMin.1
  have hClosedCanon :
      G.IsClosedUnderValues (FiniteC0.canonicalValue G κ) s := by
    intro u hu v hv
    rw [hValues u] at hv
    exact (hClosed u hu) hv
  exact FiniteC0.canonicalValue_closed_strong
    G κ hStrongSteps s hClosedCanon

variable [DecidableEq RawC0CoordinateVertex]

/-- A literal finite overlap S ∩ T, viewed as a subset of S, is
strong in S whenever S carries canonical stage/value data and
T is closed under all ambient raw-host C-values.

The target subset is the full intersection, not the set of
coordinates of its vertices. -/
theorem RawC0CoordinateVertex.closed_overlap_strong_left
    (s t : Finset RawC0CoordinateVertex)
    (hsPresented : RawC0CoordinateVertex.HasStageValuePresentation s)
    (htClosed : RawC0CoordinateVertex.IsClosed t) :
    (rawC0HostGraph.pullback
      (Subtype.val : s → RawC0CoordinateVertex)).toPredimension.IsStrong
      ((Finset.univ : Finset s).filter (fun q : s => q.val ∈ t))
      (Finset.univ : Finset s) := by
  classical
  let P : Finset s :=
    (Finset.univ : Finset s).filter (fun q : s => q.val ∈ t)
  have hP : ∀ q ∈ P,
      RawC0CoordinateVertex.valueOn s q ⊆ P := by
    intro q hq r hr
    have hqt : q.val ∈ t := (Finset.mem_filter.mp hq).2
    have hrt : r.val ∈ t :=
      (htClosed q.val hqt)
        ((RawC0CoordinateVertex.mem_valueOn_iff s q r).mp hr)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hrt⟩
  exact hasCanonicalC0StageValues_closed_strong
    (rawC0HostGraph.pullback
      (Subtype.val : s → RawC0CoordinateVertex))
    (RawC0CoordinateVertex.valueOn s)
    hsPresented P hP

/-- A finite literal intersection of two C-closed, canonically
presented raw-host factors is strong in BOTH factors, even when
the two presentations use unrelated component indices.

This is a strong-base certificate for the already verified
two-sided functional free amalgamation theorem, not an assumption
that the finite union has already been presented. -/
theorem RawC0CoordinateVertex.closed_overlap_strong_both
    (s t : Finset RawC0CoordinateVertex)
    (hsPresented : RawC0CoordinateVertex.HasStageValuePresentation s)
    (htPresented : RawC0CoordinateVertex.HasStageValuePresentation t)
    (hsClosed : RawC0CoordinateVertex.IsClosed s)
    (htClosed : RawC0CoordinateVertex.IsClosed t) :
    (rawC0HostGraph.pullback
      (Subtype.val : s → RawC0CoordinateVertex)).toPredimension.IsStrong
      ((Finset.univ : Finset s).filter (fun q : s => q.val ∈ t))
      (Finset.univ : Finset s) ∧
    (rawC0HostGraph.pullback
      (Subtype.val : t → RawC0CoordinateVertex)).toPredimension.IsStrong
      ((Finset.univ : Finset t).filter (fun q : t => q.val ∈ s))
      (Finset.univ : Finset t) := by
  exact ⟨RawC0CoordinateVertex.closed_overlap_strong_left
      s t hsPresented htClosed,
    RawC0CoordinateVertex.closed_overlap_strong_left
      t s htPresented hsClosed⟩

end FiniteUnaryCoordinates
end BigHrushovski
