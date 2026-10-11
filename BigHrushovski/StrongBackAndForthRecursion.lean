import BigHrushovski.StrongBackAndForthLimit

/-!
# Recursion from finite back-and-forth steps to a graph isomorphism

Assume every finite strong partial isomorphism has a finite strong
extension including prescribed next source and target vertices.
Ordinary recursion produces a coherent sequence. It covers both
countable vertex sets and the already verified union theorem gives
a bijective induced graph isomorphism.

This is conditional only on the finite joint extension property;
the construction of that joint step from the local forth/back
lemmas remains separate.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- An abstract finite joint step, demanding real inclusion of the
next source and target vertex without losing old map values. -/
def HasJointSteps (M N : GraphOn ℕ) : Prop :=
  ∀ (k : ℕ) (p : FiniteStrongPartialIso M N),
    ∃ q : FiniteStrongPartialIso M N,
      Extends p q ∧ k ∈ q.source ∧ k ∈ q.target

/-- Recursively select finite partial isomorphisms satisfying each
prescribed two-sided extension requirement. -/
noncomputable def chainOfJointSteps
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) :
    ℕ → FiniteStrongPartialIso M N :=
  Nat.rec p0 (fun k p => Classical.choose (hJoint k p))

theorem chainOfJointSteps_step
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) (k : ℕ) :
    Extends (chainOfJointSteps p0 hJoint k)
      (chainOfJointSteps p0 hJoint (k + 1)) := by
  change Extends (chainOfJointSteps p0 hJoint k)
    (Classical.choose (hJoint k (chainOfJointSteps p0 hJoint k)))
  exact (Classical.choose_spec
    (hJoint k (chainOfJointSteps p0 hJoint k))).1

theorem chainOfJointSteps_source_covers
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) (x : ℕ) :
    ∃ n, x ∈ (chainOfJointSteps p0 hJoint n).source := by
  refine ⟨x + 1, ?_⟩
  change x ∈
    (Classical.choose (hJoint x (chainOfJointSteps p0 hJoint x))).source
  exact (Classical.choose_spec
    (hJoint x (chainOfJointSteps p0 hJoint x))).2.1

theorem chainOfJointSteps_target_covers
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) (y : ℕ) :
    ∃ n, y ∈ (chainOfJointSteps p0 hJoint n).target := by
  refine ⟨y + 1, ?_⟩
  change y ∈
    (Classical.choose (hJoint y (chainOfJointSteps p0 hJoint y))).target
  exact (Classical.choose_spec
    (hJoint y (chainOfJointSteps p0 hJoint y))).2.2

/-- A finite joint extension property supplies a genuine induced graph
isomorphism, not merely a one-sided graph embedding. -/
noncomputable def equivOfJointSteps
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) : ℕ ≃ ℕ :=
  unionEquiv (chainOfJointSteps p0 hJoint)
    (chainOfJointSteps_step p0 hJoint)
    (chainOfJointSteps_source_covers p0 hJoint)
    (chainOfJointSteps_target_covers p0 hJoint)

theorem equivOfJointSteps_induced
    (p0 : FiniteStrongPartialIso M N)
    (hJoint : HasJointSteps M N) (x y : ℕ) :
    M.adj x y ↔
      N.adj (equivOfJointSteps p0 hJoint x)
        (equivOfJointSteps p0 hJoint y) :=
  unionEquiv_induced (chainOfJointSteps p0 hJoint)
    (chainOfJointSteps_step p0 hJoint)
    (chainOfJointSteps_source_covers p0 hJoint)
    (chainOfJointSteps_target_covers p0 hJoint) x y

/-- The empty strong partial isomorphism starts back-and-forth in any
pair of two-sparse graphs. Consequently the joint-step property
implies an induced isomorphism of their countable carriers. -/
theorem exists_induced_equiv_of_joint_steps
    (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hJoint : HasJointSteps M N) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      M.adj x y ↔ N.adj (e x) (e y) := by
  let p0 : FiniteStrongPartialIso M N :=
    FiniteStrongPartialIso.empty M N hSparseM hSparseN
  exact ⟨equivOfJointSteps p0 hJoint,
    equivOfJointSteps_induced p0 hJoint⟩

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
