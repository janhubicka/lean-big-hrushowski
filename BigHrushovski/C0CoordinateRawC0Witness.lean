import BigHrushovski.C0CoordinateBoundedSupportedFinite
import BigHrushovski.C0CoordinateOrderedAgeBridge

/-!
# Finite C₀ presentations witnessing actual complete coordinate codes

A bounded, fully supported incidence record need not belong to the
functional C₀ age. We therefore retain an explicit finite C₀
presentation behind a *one-generated* coordinate code.

The witness is a finite graph, a chronological component index
whose steps are minimal strong, an increasing coordinate labelling,
and a generating vertex. The pointed code is restricted to the full
canonical unary closure of that vertex, not an arbitrary subset.

Chronological order is NOT the stronger closure-respecting order of
the manuscript: the latter must use coherent chosen local ordered
types. We call these records *raw canonical generated codes* to avoid
declaring the missing global ordered-age theorem by definition.

The results below prove the actual full-support, root-generation,
and finite-bounded-fibre properties and retain the finite induced-age
certificates. They are intermediate steps toward W, not W itself.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- A literal finite canonical presentation in the sparse C₀
minimal-strong component age, with explicit chronological order.
No coherent choice of an internal order is assumed. -/
structure FiniteChronologicalC0 (m levels : ℕ) where
  graph : GraphOn (Fin m)
  component : Fin m → Fin levels
  minimalSteps : ∀ k : ℕ, k < levels →
    graph.toPredimension.IsMinimalStrongStep
      (FiniteC0.oldStage component k)
      (FiniteC0.oldStage component (k + 1))
  chronological : ChronologicalBlockOrder component

/-- The complete pointed coordinate code of the literal
one-generated closure C(a) from a finite C₀ presentation. -/
noncomputable def FiniteChronologicalC0.generatedCode
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) : LiteralPointedCode :=
  let C := FiniteC0.canonicalValue p.graph p.component
  (literalPointedCode p.graph C e a).restrictTo
    ((C a).image e)
    (coordinateImage_subset_labelSupport e (C a))
    (e a) ((mem_coordinateImage_iff e (C a) a).mpr
      (FiniteC0.canonicalValue_mem_self p.graph p.component a))

/-- The indicated root generates precisely the whole displayed
code, including every member of its complete C-value. -/
theorem FiniteChronologicalC0.generatedCode_root
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.generatedCode e a).IsGeneratedByPoint := by
  exact literalPointedCode_restrict_generated
    p.graph (FiniteC0.canonicalValue p.graph p.component) e a
    (FiniteC0.canonicalValue_mem_self p.graph p.component a)

/-- Every generated code from a concrete finite presentation has
complete graph and C-incidence matrices supported on its carrier. -/
theorem FiniteChronologicalC0.generatedCode_wellSupported
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.generatedCode e a).WellSupported := by
  unfold FiniteChronologicalC0.generatedCode
  exact LiteralPointedCode.restrictTo_wellSupported
    (literalPointedCode p.graph
      (FiniteC0.canonicalValue p.graph p.component) e a)
    ((FiniteC0.canonicalValue p.graph p.component a).image e)
    (coordinateImage_subset_labelSupport e
      (FiniteC0.canonicalValue p.graph p.component a))
    (e a) ((mem_coordinateImage_iff e
      (FiniteC0.canonicalValue p.graph p.component a) a).mpr
        (FiniteC0.canonicalValue_mem_self p.graph p.component a))

/-- The induced one-generated finite structure retains chronological
component order, even when some original component stages vanish. -/
theorem FiniteChronologicalC0.generatedCode_induced_chronological
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (a : Fin m) :
    ChronologicalBlockOrder
      (FiniteC0.restrictIndex p.component
        (FiniteC0.canonicalValue p.graph p.component a)) := by
  exact chronologicalBlockOrder_restrict p.component
    (FiniteC0.canonicalValue p.graph p.component a) p.chronological

/-- The induced structure inherits each component step either as a
minimal-strong step or as an empty step, exactly as required by the
finite hereditary-age theorem. No artificial renumbering is assumed. -/
theorem FiniteChronologicalC0.generatedCode_induced_minimalSteps
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (a : Fin m) (k : ℕ) (hk : k < levels) :
    let s := FiniteC0.canonicalValue p.graph p.component a
    let H := p.graph.pullback (Subtype.val : s → Fin m)
    let κs := FiniteC0.restrictIndex p.component s
    FiniteC0.oldStage κs (k+1) = FiniteC0.oldStage κs k ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κs k) (FiniteC0.oldStage κs (k+1)) := by
  exact FiniteC0.canonicalValue_oneGenerated_restrict_minimalSteps
    p.graph p.component p.minimalSteps a k hk

/-- There exists an actual finite canonical C₀ presentation and
increasing coordinate assignment generating this complete code.
The definition deliberately does NOT certify the final selected
internal orders, so it is weaker than manuscript-permitted W codes. -/
def LiteralPointedCode.IsRawC0Generated (q : LiteralPointedCode) : Prop :=
  ∃ (m levels : ℕ) (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m),
    q = p.generatedCode e a

/-- Every code with a finite C₀ presentation witness is genuinely
one-generated; mere nonempty or C-closed support would not suffice. -/
theorem LiteralPointedCode.rawC0Generated_root
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated) :
    q.IsGeneratedByPoint := by
  rcases hq with ⟨m, levels, p, e, a, heq⟩
  rw [heq]
  exact p.generatedCode_root e a

/-- Full support is automatic for an actually presented code,
rather than a hidden assumption on an arbitrary code record. -/
theorem LiteralPointedCode.rawC0Generated_wellSupported
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated) :
    q.WellSupported := by
  rcases hq with ⟨m, levels, p, e, a, heq⟩
  rw [heq]
  exact p.generatedCode_wellSupported e a

/-- A raw canonical generated code with all coordinates below N. -/
def BoundedRawC0GeneratedCode (N : ℕ) : Type :=
  {q : LiteralPointedCode //
    q.IsRawC0Generated ∧ q.support ⊆ Finset.range N}

/-- At each finite coordinate bound there are only finitely many
RAW canonical one-generated codes. This uses the four-field
complete-code finiteness theorem, not a count of unpointed types. -/
theorem finite_boundedRawC0GeneratedCode (N : ℕ) :
    Finite (BoundedRawC0GeneratedCode N) := by
  classical
  let f : BoundedRawC0GeneratedCode N →
      BoundedWellSupportedCode N :=
    fun q => ⟨q.val, ⟨q.val.rawC0Generated_wellSupported q.property.1,
      q.property.2⟩⟩
  have hf : Function.Injective f := by
    intro q r heq
    have hFields : q.val = r.val :=
      congrArg (fun z : BoundedWellSupportedCode N => z.val) heq
    exact Subtype.ext hFields
  letI : Finite (BoundedWellSupportedCode N) :=
    finite_boundedWellSupportedCode N
  exact Finite.of_injective f hf

end FiniteUnaryCoordinates
end BigHrushovski
