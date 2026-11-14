import BigHrushovski.C0FunctionalBackAndForthLimit

/-!
# Track A: closed functional back-and-forth from finite joint steps

The existing finite strong partial isomorphisms and their countable
back-and-forth limit are reused. A closed functional partial isomorphism
has finite source and target domains closed under the entire unary
operations, and its graph equivalence preserves full unary membership.

Assuming each such map can be extended to include any prescribed
source and target vertex, ordinary recursion gives a coherent
exhaustive sequence. The previously certified functional union
theorem gives one bijection of the countable carriers preserving
both induced adjacency and the complete unary functions. This
bijection extends the given initial finite partial isomorphism.

The joint finite extension property is an explicit hypothesis here;
it remains to be proved using the arbitrary-closed-base functional
extension theorem. No uniform internal ordering is chosen.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

/-- Finite induced graph isomorphisms between closed substructures,
with the exact complete unary relation preserved. -/
structure FiniteClosedFunctionalPartialIso
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ) where
  graph : FiniteStrongPartialIso M N
  sourceClosed : M.IsClosedUnderValues CM graph.source
  targetClosed : N.IsClosedUnderValues CN graph.target
  fullValues : PreservesCompleteUnaryOnSource CM CN graph

namespace FiniteClosedFunctionalPartialIso

variable {M N : GraphOn ℕ}
variable {CM CN : ℕ → Finset ℕ}

/-- The existing graph extension relation already captures the
pointwise compatibility required between two fully functional
partial isomorphisms; each endpoint separately carries the
complete unary and closedness certificates. -/
def Extends (p q : FiniteClosedFunctionalPartialIso M N CM CN) : Prop :=
  FiniteStrongPartialIso.Extends p.graph q.graph

/-- Every prescribed source/target label can be included in a later
finite closed functional partial isomorphism. The hypothesis is
intentionally independent of any selected component chronology. -/
def HasJointSteps
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ) : Prop :=
  ∀ k : ℕ, ∀ p : FiniteClosedFunctionalPartialIso M N CM CN,
    ∃ q : FiniteClosedFunctionalPartialIso M N CM CN,
      Extends p q ∧ k ∈ q.graph.source ∧ k ∈ q.graph.target

/-- Classical recursion on the finite joint-step choices. -/
noncomputable def chain
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) :
    ℕ → FiniteClosedFunctionalPartialIso M N CM CN :=
  Nat.rec p0 (fun k p => Classical.choose (hJoint k p))

/-- The graph components of the chosen chain extend one another
with literal pointwise agreement. -/
theorem chain_graph_step
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) (k : ℕ) :
    FiniteStrongPartialIso.Extends
      (chain p0 hJoint k).graph
      (chain p0 hJoint (k + 1)).graph := by
  change FiniteStrongPartialIso.Extends
    (chain p0 hJoint k).graph
    (Classical.choose (hJoint k (chain p0 hJoint k))).graph
  exact (Classical.choose_spec
    (hJoint k (chain p0 hJoint k))).1

theorem chain_source_covers
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) (x : ℕ) :
    ∃ n : ℕ, x ∈ (chain p0 hJoint n).graph.source := by
  refine ⟨x + 1, ?_⟩
  change x ∈
    (Classical.choose (hJoint x (chain p0 hJoint x))).graph.source
  exact (Classical.choose_spec
    (hJoint x (chain p0 hJoint x))).2.1

theorem chain_target_covers
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) (y : ℕ) :
    ∃ n : ℕ, y ∈ (chain p0 hJoint n).graph.target := by
  refine ⟨y + 1, ?_⟩
  change y ∈
    (Classical.choose (hJoint y (chain p0 hJoint y))).graph.target
  exact (Classical.choose_spec
    (hJoint y (chain p0 hJoint y))).2.2

/-- The limit map is precisely the previously certified graph
back-and-forth union applied to the underlying finite graph maps. -/
noncomputable def limitEquiv
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) : ℕ ≃ ℕ :=
  FiniteStrongPartialIso.unionEquiv
    (fun n => (chain p0 hJoint n).graph)
    (chain_graph_step p0 hJoint)
    (chain_source_covers p0 hJoint)
    (chain_target_covers p0 hJoint)

/-- The very same limit map induces an isomorphism of the complete
set-valued unary structures. -/
theorem limitEquiv_completeUnary
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) (x : ℕ) :
    CN (limitEquiv p0 hJoint x) =
      (CM x).image (limitEquiv p0 hJoint) := by
  exact FiniteStrongPartialIso.unionEquiv_completeUnary
    CM CN (fun n => (chain p0 hJoint n).graph)
    (chain_graph_step p0 hJoint)
    (chain_source_covers p0 hJoint)
    (chain_target_covers p0 hJoint)
    (fun n => (chain p0 hJoint n).sourceClosed)
    (fun n => (chain p0 hJoint n).targetClosed)
    (fun n => (chain p0 hJoint n).fullValues) x

theorem limitEquiv_induced
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) (x y : ℕ) :
    M.adj x y ↔
      N.adj (limitEquiv p0 hJoint x)
        (limitEquiv p0 hJoint y) := by
  exact FiniteStrongPartialIso.unionEquiv_induced
    (fun n => (chain p0 hJoint n).graph)
    (chain_graph_step p0 hJoint)
    (chain_source_covers p0 hJoint)
    (chain_target_covers p0 hJoint) x y

/-- The limit extends the initial finite functional map pointwise. -/
theorem limitEquiv_extends_initial
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN)
    (x : ℕ) (hx : x ∈ p0.graph.source) :
    limitEquiv p0 hJoint x =
      (p0.graph.equiv ⟨x, hx⟩).val := by
  exact FiniteStrongPartialIso.union_at_stage
    (fun n => (chain p0 hJoint n).graph)
    (chain_graph_step p0 hJoint)
    (chain_source_covers p0 hJoint) 0 hx

/-- Conditional functional homogeneity/uniqueness. Under the finite
closed functional joint-step property every given finite closed
functional partial isomorphism extends to a full countable
isomorphism preserving the graph and complete unary operation. -/
theorem exists_functional_equiv_extending
    (p0 : FiniteClosedFunctionalPartialIso M N CM CN)
    (hJoint : HasJointSteps M N CM CN) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ, M.adj x y ↔ N.adj (e x) (e y)) ∧
      (∀ x : ℕ, CN (e x) = (CM x).image e) ∧
      (∀ x : ℕ, ∀ hx : x ∈ p0.graph.source,
        e x = (p0.graph.equiv ⟨x, hx⟩).val) := by
  refine ⟨limitEquiv p0 hJoint, ?_, ?_, ?_⟩
  · exact limitEquiv_induced p0 hJoint
  · exact limitEquiv_completeUnary p0 hJoint
  · exact limitEquiv_extends_initial p0 hJoint

end FiniteClosedFunctionalPartialIso
end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
