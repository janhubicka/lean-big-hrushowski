import BigHrushovski.StrongBackAndForthLimit
import BigHrushovski.CFDClosedChain

/-!
# Reusable strict d-closed back-and-forth recursion

The C_F countable recognition argument requires finite induced partial
isomorphisms with *globally strictly d-closed* source and target.
A weakly strong partial map from the C_0 proof is insufficient.

Rather than copy the already verified finite-image and infinite-union
machinery, we retain the strict d-closed invariant in a separate
partial-isomorphism structure, then forget it only when taking the
coherent union. The existing union theorem depends solely on the
underlying induced maps, exact extension of values, and coverage.

The theorem below is conditional on a *strict* joint-step property.
Producing each such step from the real C_F finite response certificate
is a distinct obligation. Neither this module nor the C_0 uniqueness
theorem proves it automatically.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- A globally strictly d-closed finite subgraph is also
globally weakly strong. The converse is false in general. -/
theorem globallyStrong_of_globallyDClosed
    (M : GraphOn ℕ) (a : Finset ℕ)
    (ha : M.toPredimension.IsGloballyDClosed a) :
    M.toPredimension.IsGloballyStrong a := by
  intro b hab
  refine ⟨hab, ?_⟩
  intro c hac hcb
  by_cases hca : c = a
  · subst c
    exact le_refl _
  · exact le_of_lt (ha c hac hca)

/-- Finite induced partial isomorphisms whose source and image
are both globally strictly d-closed. Unlike the C_0 partial
isomorphism, the invariant cannot be weakened to strongness. -/
structure PartialIso (M N : GraphOn ℕ) where
  source : Finset ℕ
  target : Finset ℕ
  equiv : {x : ℕ // x ∈ source} ≃ {x : ℕ // x ∈ target}
  source_global : M.toPredimension.IsGloballyDClosed source
  target_global : N.toPredimension.IsGloballyDClosed target
  induced : ∀ x y : {x : ℕ // x ∈ source},
    M.adj x.val y.val ↔ N.adj (equiv x).val (equiv y).val

namespace PartialIso

variable {M N : GraphOn ℕ}

/-- Forget strictness solely for the generic coherent-union API.
The actual finite recursion keeps the strictly closed invariant. -/
def toStrong (p : PartialIso M N) :
    FiniteCatalogue.FiniteStrongPartialIso M N where
  source := p.source
  target := p.target
  equiv := p.equiv
  source_global := globallyStrong_of_globallyDClosed M p.source p.source_global
  target_global := globallyStrong_of_globallyDClosed N p.target p.target_global
  induced := p.induced

/-- Exact extension of the old map, including both literal
finite-domain inclusions; projected to the common union interface. -/
def Extends (p q : PartialIso M N) : Prop :=
  FiniteCatalogue.FiniteStrongPartialIso.Extends p.toStrong q.toStrong

/-- Joint strict d-closed extension over any prescribed next source
and target vertex. This is the *only* hypothesis of the recursion;
it must later be derived from finite C_F extension responses. -/
def HasJointSteps (M N : GraphOn ℕ) : Prop :=
  ∀ (k : ℕ) (p : PartialIso M N),
    ∃ q : PartialIso M N,
      Extends p q ∧ k ∈ q.source ∧ k ∈ q.target

/-- The empty strict partial isomorphism requires global strict
d-closedness of the empty sets on *both* sides. This condition
is not implied by finite strictly closed coverage alone. -/
noncomputable def empty (M N : GraphOn ℕ)
    (hEmptyM : M.toPredimension.IsGloballyDClosed ∅)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    PartialIso M N where
  source := ∅
  target := ∅
  equiv := Equiv.refl _
  source_global := hEmptyM
  target_global := hEmptyN
  induced := by
    intro x y
    have hNone : ∀ z : ℕ, z ∉ (∅ : Finset ℕ) := by simp
    exact (hNone x.val x.property).elim

/-- Choose a coherent chain, preserving strict d-closedness
at every finite stage. -/
noncomputable def chain (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) : ℕ → PartialIso M N :=
  Nat.rec p0 (fun k p => Classical.choose (hJoint k p))

theorem chain_step (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (k : ℕ) :
    Extends (chain p0 hJoint k)
      (chain p0 hJoint (k + 1)) := by
  change Extends (chain p0 hJoint k)
    (Classical.choose (hJoint k (chain p0 hJoint k)))
  exact (Classical.choose_spec
    (hJoint k (chain p0 hJoint k))).1

theorem chain_source_covers (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (x : ℕ) :
    ∃ n : ℕ, x ∈ (chain p0 hJoint n).source := by
  refine ⟨x + 1, ?_⟩
  change x ∈ (Classical.choose
    (hJoint x (chain p0 hJoint x))).source
  exact (Classical.choose_spec
    (hJoint x (chain p0 hJoint x))).2.1

theorem chain_target_covers (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (y : ℕ) :
    ∃ n : ℕ, y ∈ (chain p0 hJoint n).target := by
  refine ⟨y + 1, ?_⟩
  change y ∈ (Classical.choose
    (hJoint y (chain p0 hJoint y))).target
  exact (Classical.choose_spec
    (hJoint y (chain p0 hJoint y))).2.2

/-- The old strong-back-and-forth union machinery can be reused:
only at this final interface do we forget strict d-closedness. -/
noncomputable def strongChain (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) :
    ℕ → FiniteCatalogue.FiniteStrongPartialIso M N :=
  fun n => (chain p0 hJoint n).toStrong

theorem strongChain_step (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (k : ℕ) :
    FiniteCatalogue.FiniteStrongPartialIso.Extends
      (strongChain p0 hJoint k)
      (strongChain p0 hJoint (k + 1)) :=
  chain_step p0 hJoint k

theorem strongChain_source_covers (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (x : ℕ) :
    ∃ n : ℕ, x ∈ (strongChain p0 hJoint n).source :=
  chain_source_covers p0 hJoint x

theorem strongChain_target_covers (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (y : ℕ) :
    ∃ n : ℕ, y ∈ (strongChain p0 hJoint n).target :=
  chain_target_covers p0 hJoint y

/-- The strictly closed joint-step property yields an actual
bijection preserving and reflecting edges and nonedges. -/
noncomputable def equivOfJointSteps (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) : ℕ ≃ ℕ :=
  FiniteCatalogue.FiniteStrongPartialIso.unionEquiv
    (strongChain p0 hJoint)
    (strongChain_step p0 hJoint)
    (strongChain_source_covers p0 hJoint)
    (strongChain_target_covers p0 hJoint)

theorem equivOfJointSteps_induced (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N) (x y : ℕ) :
    M.adj x y ↔ N.adj
      (equivOfJointSteps p0 hJoint x)
      (equivOfJointSteps p0 hJoint y) :=
  FiniteCatalogue.FiniteStrongPartialIso.unionEquiv_induced
    (strongChain p0 hJoint)
    (strongChain_step p0 hJoint)
    (strongChain_source_covers p0 hJoint)
    (strongChain_target_covers p0 hJoint) x y

/-- The union extends every value of the initial strictly closed
partial isomorphism. -/
theorem equivOfJointSteps_initial (p0 : PartialIso M N)
    (hJoint : HasJointSteps M N)
    (x : {x : ℕ // x ∈ p0.source}) :
    equivOfJointSteps p0 hJoint x.val =
      (p0.equiv x).val := by
  change FiniteCatalogue.FiniteStrongPartialIso.unionToFun
    (strongChain p0 hJoint)
    (strongChain_source_covers p0 hJoint) x.val =
      (p0.equiv x).val
  exact FiniteCatalogue.FiniteStrongPartialIso.union_at_stage
    (strongChain p0 hJoint)
    (strongChain_step p0 hJoint)
    (strongChain_source_covers p0 hJoint)
    0 x.property

/-- The strict back-and-forth uniqueness criterion, still
conditional on the exact strict joint-step theorem. -/
theorem exists_induced_equiv_of_joint_steps
    (M N : GraphOn ℕ)
    (hEmptyM : M.toPredimension.IsGloballyDClosed ∅)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅)
    (hJoint : HasJointSteps M N) :
    ∃ e : ℕ ≃ ℕ,
      ∀ x y : ℕ, M.adj x y ↔ N.adj (e x) (e y) := by
  let p0 := empty M N hEmptyM hEmptyN
  exact ⟨equivOfJointSteps p0 hJoint,
    equivOfJointSteps_induced p0 hJoint⟩

end PartialIso
end CFDClosedBackAndForth
end BigHrushovski
