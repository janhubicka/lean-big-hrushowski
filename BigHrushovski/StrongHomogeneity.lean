import BigHrushovski.StrongJointExtension
import BigHrushovski.GenericStrongClosure

/-!
# Strong homogeneity and uniqueness of the countable generic

The finite joint-step theorem removes the final existence hypothesis
from the alternating strong back-and-forth recursion. Starting the
recursion from an arbitrary finite globally strong partial
isomorphism also shows that the resulting countable automorphism
retains its prescribed values.

For the concrete generic graph built by fair finite recursion,
this proves strong homogeneity and uniqueness among countable
2-sparse graphs with finite strong covers and the finite strong
extension property.

This identifies the concrete graph with the strong Fraïssé limit
of the 2-sparse strong age. The functional closure expansion,
Ramsey arguments and Ellentuck-space axioms are independent
formalization tasks.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- The induced union isomorphism extends the initial finite
globally strong partial isomorphism pointwise. -/
theorem equivOfJointSteps_initial
    (p : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N)
    (x : {x : ℕ // x ∈ p.source}) :
    (equivOfJointSteps p hJoint x.val) =
      (p.equiv x).val := by
  change unionToFun (chainOfJointSteps p hJoint)
    (chainOfJointSteps_source_covers p hJoint) x.val =
      (p.equiv x).val
  exact union_at_stage (chainOfJointSteps p hJoint)
    (chainOfJointSteps_step p hJoint)
    (chainOfJointSteps_source_covers p hJoint) 0 x.property

/-- Every finite strong partial isomorphism of a countable 2-sparse
generic extends to a total induced automorphism. -/
theorem strongHomogeneous_of_strongExtension
    (M : GraphOn ℕ)
    (hSparse : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hCover : Predimension.FiniteStrongCover M.toPredimension)
    (hExt : HasStrongExtensionProperty M)
    (p : FiniteStrongPartialIso M M) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ, M.adj x y ↔ M.adj (e x) (e y)) ∧
      (∀ x : {x : ℕ // x ∈ p.source},
        e x.val = (p.equiv x).val) := by
  let hJoint : HasJointSteps M M :=
    hasJointSteps_of_strongExtension M M
      hSparse hSparse hCover hCover hExt hExt
  exact ⟨equivOfJointSteps p hJoint,
    equivOfJointSteps_induced p hJoint,
    equivOfJointSteps_initial p hJoint⟩

end FiniteStrongPartialIso

/-- The concrete fair-recursion graph is unique up to an induced
isomorphism among countable structures having the strong Fraïssé
extension property and finite strong covers. -/
theorem genericTwoSparseGraph_unique
    (N : GraphOn ℕ)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCoverN : Predimension.FiniteStrongCover N.toPredimension)
    (hExtN : HasStrongExtensionProperty N) :
    ∃ e : ℕ ≃ ℕ,
      ∀ x y : ℕ,
        genericTwoSparseGraph.adj x y ↔
          N.adj (e x) (e y) :=
  FiniteStrongPartialIso.exists_induced_equiv_of_strongExtension
    genericTwoSparseGraph N
    genericTwoSparseGraph_sparse hSparseN
    genericTwoSparseGraph_finiteStrongCover hCoverN
    genericTwoSparseGraph_strongExtension hExtN

/-- Strong homogeneity of the concrete countable 2-sparse generic:
every finite globally strong induced partial isomorphism extends to
a total induced automorphism of the whole graph. -/
theorem genericTwoSparseGraph_strongHomogeneous
    (p : FiniteStrongPartialIso
      genericTwoSparseGraph genericTwoSparseGraph) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        genericTwoSparseGraph.adj x y ↔
          genericTwoSparseGraph.adj (e x) (e y)) ∧
      (∀ x : {x : ℕ // x ∈ p.source},
        e x.val = (p.equiv x).val) :=
  FiniteStrongPartialIso.strongHomogeneous_of_strongExtension
    genericTwoSparseGraph
    genericTwoSparseGraph_sparse
    genericTwoSparseGraph_finiteStrongCover
    genericTwoSparseGraph_strongExtension p

end FiniteCatalogue
end BigHrushovski
