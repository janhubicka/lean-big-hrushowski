import BigHrushovski.HrushovskiEllentuckFiniteSupportCompletion
import Mathlib.Topology.Constructions

/-!
# Closedness of the complete-support domain codes

Let each vertex have a finite *complete* support in a level set.
Encode subsets of vertices by Boolean characteristic functions,
with the discrete topology on Bool and the product topology on
Vertex → Bool. The family of complete-support domains is closed.

The obstruction is finite: if X is not a complete-support domain,
some v outside X has its entire finite support represented among
finitely many vertices already in X. Fixing the finitely many
characteristic coordinates for those witnesses and v gives an open
neighbourhood disjoint from every complete-support domain.

This is closedness of the **support-domain family**, not closedness
of the approximation-code image of functional embeddings, and it
does not establish the A.1--A.4 Ramsey-space axioms.
-/

namespace BigHrushovski

universe u v

local instance boolCodeTopology : TopologicalSpace Bool := ⊥
local instance boolCodeDiscrete : DiscreteTopology Bool := ⟨rfl⟩
local instance boolCodeProductTopology {V : Type*} :
    TopologicalSpace (V → Bool) := Pi.topologicalSpace

namespace Ellentuck

variable {Vertex : Type u} {Level : Type v}

/-- All characteristic functions of complete-support domains.  The
source level set is not required to be uniquely determined. -/
def supportDomainCodes
    (support : Vertex → Finset Level) : Set (Vertex → Bool) :=
  {b | ∃ S : Set Level,
    ∀ x, (b x = true ↔ x ∈ supportDomain support S)}

/-- A characteristic function represents a complete-support domain
exactly when its vertex set is fixed by the finite-character support
completion. No singleton-support witnesses are needed. -/
theorem mem_supportDomainCodes_iff_fixed
    (support : Vertex → Finset Level) (b : Vertex → Bool) :
    b ∈ supportDomainCodes support ↔
      supportCompletion support {x | b x = true} =
        {x | b x = true} := by
  constructor
  · rintro ⟨S, hS⟩
    have hX : {x | b x = true} = supportDomain support S := by
      ext x
      exact hS x
    rw [hX]
    exact supportCompletion_of_domain support S
  · intro hFixed
    refine ⟨supportLevels support {x | b x = true}, ?_⟩
    intro x
    change b x = true ↔
      x ∈ supportCompletion support {y | b y = true}
    rw [hFixed]
    rfl

/-- The support-domain characteristic functions form a closed subset
of the product of discrete Boolean coordinate spaces. This is a
finite-character topological theorem, not the Ellentuck closedness
axiom for a space of self-embeddings. -/
theorem isClosed_supportDomainCodes
    (support : Vertex → Finset Level) :
    IsClosed (supportDomainCodes support) := by
  classical
  rw [← isOpen_compl_iff]
  rw [isOpen_pi_iff]
  intro b hb
  let X : Set Vertex := {x | b x = true}
  have hNotFixed : supportCompletion support X ≠ X := by
    intro hFixed
    exact hb ((mem_supportDomainCodes_iff_fixed support b).2 hFixed)
  have hBad :
      ∃ x : Vertex, x ∈ supportCompletion support X ∧ x ∉ X := by
    by_contra h
    push_neg at h
    apply hNotFixed
    apply Set.Subset.antisymm
    · intro x hx
      exact h x hx
    · exact subset_supportCompletion support X
  obtain ⟨x, hx, hxNot⟩ := hBad
  obtain ⟨s, hsX, hxs⟩ :=
    (mem_supportCompletion_iff_finite_witness support X x).mp hx
  -- Fix every vertex of the finite witness set, as well as x itself.
  refine ⟨insert x s, (fun i => {b i}), ?_, ?_⟩
  · intro i hi
    constructor
    · exact isOpen_discrete _
    · simp
  · intro c hc
    show c ∈ (supportDomainCodes support)ᶜ
    intro hcCode
    let Y : Set Vertex := {y | c y = true}
    have hsY : (↑s : Set Vertex) ⊆ Y := by
      intro y hy
      have hcy : c y = b y := by
        have hyI : y ∈ insert x s := Finset.mem_insert_of_mem hy
        simpa using hc y hyI
      change c y = true
      rw [hcy]
      exact hsX hy
    have hxY : x ∈ supportCompletion support Y :=
      supportCompletion_mono support hsY hxs
    have hFixed : supportCompletion support Y = Y :=
      (mem_supportDomainCodes_iff_fixed support c).mp hcCode
    have hcx : c x = true := by
      have hxIn : x ∈ Y := by
        rw [← hFixed]
        exact hxY
      exact hxIn
    have hcxEq : c x = b x := by
      simpa using hc x (Finset.mem_insert_self x s)
    apply hxNot
    change b x = true
    rw [← hcxEq]
    exact hcx

end Ellentuck

namespace CFCoherentTower

/-- Closed family of full b-generated support domains on the
actual countable C_F birth-labelled carrier. -/
def birthLevelDomainCodes (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Set (Vertex F K → Bool) :=
  Ellentuck.supportDomainCodes (birthLevelSupport F K)

theorem isClosed_birthLevelDomainCodes
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    IsClosed (birthLevelDomainCodes F K) :=
  Ellentuck.isClosed_supportDomainCodes (birthLevelSupport F K)

end CFCoherentTower
end BigHrushovski
