import BigHrushovski.C0CoordinateFiniteStageValueTransport
import BigHrushovski.C0CoordinateRawHostGeneratedOccurrence
import BigHrushovski.C0CoordinateFiniteAge

/-!
# Finite stage/value witness on each raw one-generated closure

Each vertex of the preliminary raw coordinate host has a complete
one-generated finite C₀ code coming from an actual finite minimal-
strong presentation. The raw host's finite C-value is equivalent
to the corresponding one-generated closure in that presentation,
including all graph and complete unary C/J incidences.

We transport the *empty-or-minimal-strong* stage witness of that
source closure to the literal finite raw-host closure. This is
the local input for the converse finite-age induction: the finite
closed union of such closures still needs a separate amalgamation
and transport argument.

No selected order on all raw codes, W, return map or Ramsey
conclusion is assumed.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- A finite closed raw-host subset carries an actual canonical
C₀ stage indexing with complete named unary values. It is a
finite stage/value witness, not merely a graph presentation.
An additional two-sparseness certificate will be needed for the
two-sided finite functional amalgamation theorem. -/
def RawC0CoordinateVertex.HasStageValuePresentation
    [DecidableEq RawC0CoordinateVertex]
    (s : Finset RawC0CoordinateVertex) : Prop :=
  HasCanonicalC0StageValues
    (rawC0HostGraph.pullback
      (Subtype.val : s → RawC0CoordinateVertex))
    (RawC0CoordinateVertex.valueOn s)

/-- The canonical C₀ value of a vertex in an induced one-generated
source closure is exactly its original complete unary value.
In particular this includes every negative as well as positive
C-incidence. -/
theorem FiniteChronologicalC0.generatedSource_mem_C_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (a : Fin m)
    (u v : FiniteC0.canonicalValue p.graph p.component a) :
    v ∈ FiniteC0.canonicalValue
      (p.graph.pullback
        (Subtype.val :
          (FiniteC0.canonicalValue p.graph p.component a) → Fin m))
      (FiniteC0.restrictIndex p.component
        (FiniteC0.canonicalValue p.graph p.component a)) u ↔
      v.val ∈ FiniteC0.canonicalValue p.graph p.component u.val := by
  classical
  let S := FiniteC0.canonicalValue p.graph p.component a
  let H := p.graph.pullback (Subtype.val : S → Fin m)
  let κS := FiniteC0.restrictIndex p.component S
  have hImage (x : S) :
      (FiniteC0.canonicalValue H κS x).image
        (Subtype.val : S → Fin m) =
      FiniteC0.canonicalValue p.graph p.component x.val :=
    FiniteC0.canonicalValue_oneGenerated_restrict_exact
      p.graph p.component a x
  constructor
  · intro hv
    have hImageMem : v.val ∈
        (FiniteC0.canonicalValue H κS u).image
          (Subtype.val : S → Fin m) :=
      Finset.mem_image.mpr ⟨v,hv,rfl⟩
    rw [hImage u] at hImageMem
    exact hImageMem
  · intro hv
    rw [← hImage u] at hv
    obtain ⟨w,hw,hEq⟩ := Finset.mem_image.mp hv
    have hwv : w = v := Subtype.ext hEq
    simpa only [hwv] using hw

/-- The literal complete raw-host unary closure of a finite
presented code has an actual canonical component index, allowing
empty steps, and its canonical finite unary values agree with the
ambient raw-host C-values ON THE NOSE.

We transport the finite restricted source presentation through the
previously verified generated-occurrence equivalence, rather than
inventing another component enumeration of the raw host. -/
theorem FiniteChronologicalC0.asRawVertex_hasStageValuePresentation
    [DecidableEq RawC0CoordinateVertex]
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    RawC0CoordinateVertex.HasStageValuePresentation
      (p.asRawVertex e a).closedValue := by
  classical
  let S : Finset (Fin m) :=
    FiniteC0.canonicalValue p.graph p.component a
  let R : Finset RawC0CoordinateVertex :=
    (p.asRawVertex e a).closedValue
  let H : GraphOn S :=
    p.graph.pullback (Subtype.val : S → Fin m)
  let K : GraphOn R :=
    rawC0HostGraph.pullback
      (Subtype.val : R → RawC0CoordinateVertex)
  let κS : S → Fin levels :=
    FiniteC0.restrictIndex p.component S
  let f : S ≃ R := p.generatedOccurrenceEquiv e a
  have hStages : ∀ k : ℕ, k < levels →
      FiniteC0.oldStage κS k = FiniteC0.oldStage κS (k+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κS k) (FiniteC0.oldStage κS (k+1)) := by
    intro k hk
    exact FiniteC0.canonicalValue_oneGenerated_restrict_minimalSteps
      p.graph p.component p.minimalSteps a k hk
  have hSource :
      HasCanonicalC0StageValues H
        (FiniteC0.canonicalValue H κS) :=
    ⟨levels,κS,hStages,fun _ => rfl⟩
  have hAdj : ∀ u v : S,
      H.adj u v ↔ K.adj (f u) (f v) := by
    intro u v
    change p.graph.adj u.val v.val ↔
      rawC0HostGraph.adj (f u).val (f v).val
    exact (p.generatedOccurrence_graph_iff e a u v).symm
  have hValues : ∀ u : S,
      (FiniteC0.canonicalValue H κS u).image f =
      RawC0CoordinateVertex.valueOn R (f u) := by
    intro u
    ext v
    let w : S := f.symm v
    have hfv : f w = v := f.apply_symm_apply v
    constructor
    · intro hv
      obtain ⟨z,hz,hzv⟩ := Finset.mem_image.mp hv
      have hzw : z = w := f.injective (hzv.trans hfv.symm)
      have hw : w ∈ FiniteC0.canonicalValue H κS u := by
        simpa only [hzw] using hz
      have hOriginal : w.val ∈
          FiniteC0.canonicalValue p.graph p.component u.val :=
        (p.generatedSource_mem_C_iff a u w).mp hw
      have hIn : (f w).val ∈ (f u).val.closedValue :=
        (p.generatedOccurrence_C_iff e a u w).mpr hOriginal
      rw [hfv] at hIn
      exact (RawC0CoordinateVertex.mem_valueOn_iff R (f u) v).mpr hIn
    · intro hv
      have hIn : v.val ∈ (f u).val.closedValue :=
        (RawC0CoordinateVertex.mem_valueOn_iff R (f u) v).mp hv
      rw [← hfv] at hIn
      have hOriginal : w.val ∈
          FiniteC0.canonicalValue p.graph p.component u.val :=
        (p.generatedOccurrence_C_iff e a u w).mp hIn
      have hw : w ∈ FiniteC0.canonicalValue H κS u :=
        (p.generatedSource_mem_C_iff a u w).mpr hOriginal
      exact Finset.mem_image.mpr ⟨w,hw,hfv⟩
  exact hasCanonicalC0StageValues_equiv
    H K (FiniteC0.canonicalValue H κS)
    (RawC0CoordinateVertex.valueOn R)
    f hAdj hValues hSource

/-- Every complete one-generated unary value of the preliminary
raw coordinate host has a genuine finite canonical stage/value
presentation, without selecting a preferred generating vertex. -/
theorem RawC0CoordinateVertex.closedValue_hasStageValuePresentation
    [DecidableEq RawC0CoordinateVertex]
    (q : RawC0CoordinateVertex) :
    RawC0CoordinateVertex.HasStageValuePresentation
      q.closedValue := by
  rcases q with ⟨code,hcode⟩
  rcases hcode with ⟨m, levels, p, e, a, hEq⟩
  subst code
  change RawC0CoordinateVertex.HasStageValuePresentation
    (p.asRawVertex e a).closedValue
  exact p.asRawVertex_hasStageValuePresentation e a

end FiniteUnaryCoordinates
end BigHrushovski
