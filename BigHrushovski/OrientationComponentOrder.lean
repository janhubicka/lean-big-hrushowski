import BigHrushovski.OrientationMinimalStep
import Mathlib.Tactic

/-!
# The dependency order of strongly connected components

The successor relation on vertices yields an intrinsic strict
partial order on strongly connected components: B precedes C if
there is a directed path from C to B, but no path back.

The relation does not depend on the choice of a vertex representing
either component. In particular, component precedence is not a
chronological order chosen in a minimal enumeration. This is the
finite relation whose linear extensions are counted in the paper's
N₀ degree formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- Proper directed reachability, excluding vertices in the
same strongly connected component. -/
def StrictSuccessor (x y : V) : Prop :=
  O.Reaches x y ∧ ¬ O.Reaches y x

theorem strictSuccessor_irrefl (x : V) :
    ¬ O.StrictSuccessor x x := by
  intro h
  exact h.2 (O.reaches_refl x)

theorem strictSuccessor_trans {x y z : V}
    (hxy : O.StrictSuccessor x y)
    (hyz : O.StrictSuccessor y z) :
    O.StrictSuccessor x z := by
  refine ⟨O.reaches_trans hxy.1 hyz.1, ?_⟩
  intro hzx
  exact hyz.2 (O.reaches_trans hzx hxy.1)

theorem strictSuccessor_asymm {x y : V}
    (hxy : O.StrictSuccessor x y) :
    ¬ O.StrictSuccessor y x := by
  intro hyx
  exact hxy.2 hyx.1

/-- Changing either representative within its strongly connected
component preserves and reflects proper directed reachability. -/
theorem strictSuccessor_transport {x x' y y' : V}
    (hxx' : O.StronglyConnected x x')
    (hyy' : O.StronglyConnected y y') :
    O.StrictSuccessor x y ↔ O.StrictSuccessor x' y' := by
  constructor
  · rintro ⟨hxy, hyx⟩
    refine ⟨O.reaches_trans hxx'.2
      (O.reaches_trans hxy hyy'.1), ?_⟩
    intro hy'x'
    exact hyx (O.reaches_trans hyy'.1
      (O.reaches_trans hy'x' hxx'.2))
  · rintro ⟨hx'y', hy'x'⟩
    refine ⟨O.reaches_trans hxx'.1
      (O.reaches_trans hx'y' hyy'.2), ?_⟩
    intro hyx
    exact hy'x' (O.reaches_trans hyy'.2
      (O.reaches_trans hyx hxx'.1))

/-- The finite set of distinct strongly connected components. -/
noncomputable def components [Fintype V] :
    Finset (Finset V) := by
  classical
  exact Finset.univ.image O.component

theorem component_mem_components [Fintype V] (x : V) :
    O.component x ∈ O.components := by
  classical
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_univ x, rfl⟩

/-- B strictly precedes C when a path runs from C down to B
and cannot return. Here B and C are actual vertex sets, not
names in a chosen enumeration. -/
def ComponentPrecedes [Fintype V]
    (B C : Finset V) : Prop :=
  ∃ lower upper : V,
    O.component lower = B ∧
    O.component upper = C ∧
    O.StrictSuccessor upper lower

theorem componentPrecedes_irrefl [Fintype V]
    (B : Finset V) :
    ¬ O.ComponentPrecedes B B := by
  rintro ⟨x, y, hx, hy, hyx⟩
  have hsc : O.StronglyConnected x y :=
    (O.stronglyConnected_iff_component_eq x y).mpr
      (hx.trans hy.symm)
  exact hyx.2 hsc.1

theorem componentPrecedes_trans [Fintype V]
    {B C D : Finset V}
    (hBC : O.ComponentPrecedes B C)
    (hCD : O.ComponentPrecedes C D) :
    O.ComponentPrecedes B D := by
  obtain ⟨x, y, hxB, hyC, hyx⟩ := hBC
  obtain ⟨z, w, hzC, hwD, hwz⟩ := hCD
  have hzy : O.StronglyConnected z y :=
    (O.stronglyConnected_iff_component_eq z y).mpr
      (hzC.trans hyC.symm)
  have hwy : O.StrictSuccessor w y :=
    (O.strictSuccessor_transport
      (O.stronglyConnected_refl w) hzy).mp hwz
  exact ⟨x, w, hxB, hwD, O.strictSuccessor_trans hwy hyx⟩

theorem componentPrecedes_asymm [Fintype V]
    {B C : Finset V}
    (hBC : O.ComponentPrecedes B C) :
    ¬ O.ComponentPrecedes C B := by
  intro hCB
  exact O.componentPrecedes_irrefl B
    (O.componentPrecedes_trans hBC hCB)

/-- Dependence between two components is equivalent to proper
reachability between any choice of representatives. -/
theorem componentPrecedes_iff_strictSuccessor [Fintype V]
    (upper lower : V) :
    O.ComponentPrecedes (O.component lower) (O.component upper) ↔
      O.StrictSuccessor upper lower := by
  constructor
  · rintro ⟨x, y, hx, hy, hyx⟩
    have hUpper : O.StronglyConnected y upper :=
      (O.stronglyConnected_iff_component_eq y upper).mpr hy
    have hLower : O.StronglyConnected x lower :=
      (O.stronglyConnected_iff_component_eq x lower).mpr hx
    exact (O.strictSuccessor_transport hUpper hLower).mp hyx
  · intro h
    exact ⟨lower, upper, rfl, rfl, h⟩

/-- Any directed path either remains in one strongly connected
component or gives a strict precedence relation between components. -/
theorem reaches_component_eq_or_precedes [Fintype V]
    {x y : V} (hxy : O.Reaches x y) :
    O.component x = O.component y ∨
      O.ComponentPrecedes (O.component y) (O.component x) := by
  by_cases hyx : O.Reaches y x
  · exact Or.inl
      ((O.stronglyConnected_iff_component_eq x y).mp ⟨hxy, hyx⟩)
  · exact Or.inr
      ((O.componentPrecedes_iff_strictSuccessor x y).mpr ⟨hxy, hyx⟩)

end FiniteOrientation
end BigHrushovski
