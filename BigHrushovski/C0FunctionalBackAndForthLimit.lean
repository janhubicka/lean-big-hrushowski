import BigHrushovski.StrongBackAndForthRecursion
import BigHrushovski.C0CountableCanonicalStages

/-!
# Track A: complete unary functions in the limit of a closed back-and-forth

The existing countable strong back-and-forth theorem constructs an
actual bijection of two countable graph carriers from a coherent
sequence of finite strong partial isomorphisms. We show that this SAME
bijection also preserves the *entire* set-valued unary function,
provided the finite partial maps have C-closed domains and ranges and
preserve full unary membership.

This is the reusable limit step of the functional Fraïssé homogeneity
argument. The finite two-sided extension step constructing the chain
from arbitrary finite closed bases remains separate.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- Complete unary membership is preserved on every finite partial
isomorphism, in both directions. The quantified vertices are those
of the *same* finite source domain; closure of that source and the
target ensures that this is equivalent to full function equality. -/
def PreservesCompleteUnaryOnSource
    (CM CN : ℕ → Finset ℕ)
    (p : FiniteStrongPartialIso M N) : Prop :=
  ∀ x y : {v : ℕ // v ∈ p.source},
    y.val ∈ CM x.val ↔
      (p.equiv y).val ∈ CN (p.equiv x).val

/-- The graph isomorphism at the end of a coherent chain of finite
closed functional partial isomorphisms preserves EVERY complete
unary value exactly. No restriction to old-neighbour sets, one-step
edges, or bounded dependency depth is made. -/
theorem unionEquiv_completeUnary
    (CM CN : ℕ → Finset ℕ)
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (hCoverTarget : ∀ y : ℕ, ∃ n, y ∈ (p n).target)
    (hSourceClosed : ∀ n,
      M.IsClosedUnderValues CM (p n).source)
    (hTargetClosed : ∀ n,
      N.IsClosedUnderValues CN (p n).target)
    (hFull : ∀ n, PreservesCompleteUnaryOnSource CM CN (p n))
    (x : ℕ) :
    CN (unionEquiv p hStep hCoverSource hCoverTarget x) =
      (CM x).image (unionEquiv p hStep hCoverSource hCoverTarget) := by
  classical
  let e : ℕ ≃ ℕ := unionEquiv p hStep hCoverSource hCoverTarget
  obtain ⟨n, hx⟩ := hCoverSource x
  let ux : {v : ℕ // v ∈ (p n).source} := ⟨x, hx⟩
  have heX : e x = ((p n).equiv ux).val :=
    union_at_stage p hStep hCoverSource n hx
  apply Finset.ext
  intro y
  constructor
  · intro hy
    have hyT : y ∈ (p n).target := by
      have hVal : y ∈ CN ((p n).equiv ux).val := by
        rw [← heX]
        exact hy
      exact hTargetClosed n
        ((p n).equiv ux).val ((p n).equiv ux).property hVal
    let vy : {v : ℕ // v ∈ (p n).target} := ⟨y, hyT⟩
    let uy : {v : ℕ // v ∈ (p n).source} :=
      (p n).equiv.symm vy
    have hVal : ((p n).equiv uy).val ∈
        CN ((p n).equiv ux).val := by
      change y ∈ CN ((p n).equiv ux).val
      rw [← heX]
      exact hy
    have huy : uy.val ∈ CM x :=
      (hFull n ux uy).mpr hVal
    have heY : e uy.val = y := by
      rw [union_at_stage p hStep hCoverSource n uy.property]
      change ((p n).equiv uy).val = y
      simp [uy, vy]
    exact Finset.mem_image.mpr ⟨uy.val, huy, heY⟩
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hzS : z ∈ (p n).source :=
      hSourceClosed n x hx hz
    let uz : {v : ℕ // v ∈ (p n).source} := ⟨z, hzS⟩
    have hVal :
        ((p n).equiv uz).val ∈
          CN ((p n).equiv ux).val :=
      (hFull n ux uz).mp hz
    have heZ : e z = ((p n).equiv uz).val :=
      union_at_stage p hStep hCoverSource n hzS
    rw [← hzy, heZ, heX]
    exact hVal

/-- A functional back-and-forth chain yields a single bijection
preserving and reflecting all graph edges, and transporting the
whole unary operation. This packages both conclusions for subsequent
functional Fraïssé homogeneity and uniqueness arguments. -/
theorem exists_functional_equiv_of_closed_chain
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ)
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (hCoverTarget : ∀ y : ℕ, ∃ n, y ∈ (p n).target)
    (hSourceClosed : ∀ n,
      M.IsClosedUnderValues CM (p n).source)
    (hTargetClosed : ∀ n,
      N.IsClosedUnderValues CN (p n).target)
    (hFull : ∀ n, PreservesCompleteUnaryOnSource CM CN (p n)) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        M.adj x y ↔ N.adj (e x) (e y)) ∧
      (∀ x : ℕ, CN (e x) = (CM x).image e) := by
  let e : ℕ ≃ ℕ :=
    unionEquiv p hStep hCoverSource hCoverTarget
  refine ⟨e, ?_, ?_⟩
  · intro x y
    exact unionEquiv_induced
      p hStep hCoverSource hCoverTarget x y
  · intro x
    exact unionEquiv_completeUnary CM CN p hStep
      hCoverSource hCoverTarget
      hSourceClosed hTargetClosed hFull x

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
