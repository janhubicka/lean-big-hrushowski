import BigHrushovski.C0UnaryFiniteStrong
import BigHrushovski.C0TaggedDependency

/-!
# Canonical unary closures in an arbitrary finite C0 block presentation

A finite block presentation is given by a component index
κ : V → Fin n. Its kth component is the fibre κ⁻¹(k), and its
kth old prefix consists of the vertices with index < k.
This encoding makes it impossible for an enumeration to omit a
vertex or assign the same vertex to two distinct components.

Direct dependencies point from the component of an endpoint of an
edge to its earlier component. The unary value C(v) is the union
of all complete components reachable from κ(v) by these directed
back edges, including the starting component.

The component and old-neighbour clauses previously required as
hypotheses by C0UnaryFiniteStrong now follow directly from this
definition. Hence whenever the finite stages are strong in their
successors, every subset closed under the canonical unary function
is strong in the entire finite graph.

No countable Fraïssé limit or ambient strong exhaustion is assumed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- The vertices appearing strictly before step k. -/
noncomputable def oldStage (κ : V → Fin n) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (κ v).val < k)

/-- The complete kth new block; it may be empty if κ has no such value. -/
noncomputable def component (κ : V → Fin n) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (κ v).val = k)

theorem mem_oldStage_iff (κ : V → Fin n) (k : ℕ) (v : V) :
    v ∈ oldStage κ k ↔ (κ v).val < k := by
  classical
  simp [oldStage]

theorem mem_component_iff (κ : V → Fin n) (k : ℕ) (v : V) :
    v ∈ component κ k ↔ (κ v).val = k := by
  classical
  simp [component]

/-- The successive finite prefixes have exactly one new fibre. -/
theorem oldStage_succ (κ : V → Fin n) (k : ℕ) :
    oldStage κ (k+1) = oldStage κ k ∪ component κ k := by
  classical
  ext v
  simp only [mem_oldStage_iff, Finset.mem_union, mem_component_iff]
  omega

theorem oldStage_zero (κ : V → Fin n) :
    oldStage κ 0 = ∅ := by
  classical
  ext v
  simp [mem_oldStage_iff]

theorem oldStage_final (κ : V → Fin n) :
    oldStage κ n = Finset.univ := by
  classical
  ext v
  simp only [mem_oldStage_iff, Finset.mem_univ, iff_true]
  exact (κ v).isLt

theorem oldStage_disjoint_component
    (κ : V → Fin n) (k : ℕ) :
    Disjoint (oldStage κ k) (component κ k) := by
  apply Finset.disjoint_left.mpr
  intro v hvOld hvNew
  have hlt : (κ v).val < k :=
    (mem_oldStage_iff κ k v).mp hvOld
  have heq : (κ v).val = k :=
    (mem_component_iff κ k v).mp hvNew
  omega

/-- A directed edge from one component to an earlier component,
witnessed by an actual graph edge between the two full blocks. -/
def backDependency (G : GraphOn V) (κ : V → Fin n)
    (i j : Fin n) : Prop :=
  j.val < i.val ∧
    ∃ u v : V, κ u = i ∧ κ v = j ∧ G.adj u v

/-- The finite set-valued unary closure on the complete vertex
carrier, obtained by following component back-edge dependencies. -/
noncomputable def canonicalValue
    (G : GraphOn V) (κ : V → Fin n) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun v => TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ u) (κ v))

theorem mem_canonicalValue_iff
    (G : GraphOn V) (κ : V → Fin n) (u v : V) :
    v ∈ canonicalValue G κ u ↔
      TaggedAmalgam.DependencyAncestor
        (backDependency G κ) (κ u) (κ v) := by
  classical
  simp [canonicalValue]

/-- Each one-generated unary closure contains the entirety of its
starting component; no vertex is selected as a special generator. -/
theorem canonicalValue_contains_component
    (G : GraphOn V) (κ : V → Fin n)
    (k : ℕ) {u : V}
    (hu : u ∈ component κ k) :
    component κ k ⊆ canonicalValue G κ u := by
  intro v hv
  have huIndex : (κ u).val = k :=
    (mem_component_iff κ k u).mp hu
  have hvIndex : (κ v).val = k :=
    (mem_component_iff κ k v).mp hv
  have hEq : κ v = κ u := Fin.ext (by omega)
  apply (mem_canonicalValue_iff G κ u v).mpr
  rw [hEq]
  exact TaggedAmalgam.DependencyAncestor.root

/-- The old neighbours of a vertex in the kth block are included
in that vertex's full unary value via a one-step back dependency. -/
theorem canonicalValue_oldNeighbour
    (G : GraphOn V) (κ : V → Fin n)
    (k : ℕ) {u v : V}
    (hu : u ∈ component κ k)
    (hv : v ∈ oldStage κ k)
    (hadj : G.adj u v) :
    v ∈ canonicalValue G κ u := by
  have hku : (κ u).val = k :=
    (mem_component_iff κ k u).mp hu
  have hkv : (κ v).val < k :=
    (mem_oldStage_iff κ k v).mp hv
  have hDep : backDependency G κ (κ u) (κ v) :=
    ⟨by omega, u, v, rfl, rfl, hadj⟩
  exact (mem_canonicalValue_iff G κ u v).mpr
    (TaggedAmalgam.DependencyAncestor.step
      TaggedAmalgam.DependencyAncestor.root hDep)

/-- A finite graph whose successive index prefixes are strong has
strong unary-closed substructures under its canonical complete
component closure. The first step is included in the hypotheses,
so empty-to-full strongness is automatic. -/
theorem canonicalValue_closed_strong
    (G : GraphOn V) (κ : V → Fin n)
    (hStep : ∀ k : ℕ, k < n →
      G.toPredimension.IsStrong
        (oldStage κ k) (oldStage κ (k+1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s) :
    G.toPredimension.IsStrong s Finset.univ := by
  classical
  have hInd : ∀ k : ℕ, k ≤ n →
      G.toPredimension.IsStrong
        (s ∩ oldStage κ k) (oldStage κ k) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [oldStage_zero κ]
        simp only [Finset.inter_empty]
        exact G.toPredimension.strong_refl ∅
    | succ k ih =>
        intro hk
        let A := oldStage κ k
        let B := component κ k
        have hOld : G.toPredimension.IsStrong (s ∩ A) A :=
          ih (by omega)
        have hAB : G.toPredimension.IsStrong A (A ∪ B) := by
          change G.toPredimension.IsStrong
            (oldStage κ k)
            (oldStage κ k ∪ component κ k)
          rw [← oldStage_succ κ k]
          exact hStep k (by omega)
        have hDisj : Disjoint A B :=
          oldStage_disjoint_component κ k
        have hWhole : ∀ u ∈ B, B ⊆ canonicalValue G κ u := by
          intro u hu
          exact canonicalValue_contains_component G κ k hu
        have hBack :
            ∀ u ∈ B, ∀ v ∈ A, G.adj u v →
              v ∈ canonicalValue G κ u := by
          intro u hu v hv hadj
          exact canonicalValue_oldNeighbour G κ k hu hv hadj
        have hCase : B ⊆ s ∨ Disjoint s B :=
          G.closedUnderValues_block_dichotomy
            (canonicalValue G κ) s B hClosed hWhole
        have hNo : B ⊆ s →
            G.NoCrossEdges A ((s ∩ A) ∪ B) :=
          G.closedUnderValues_block_noCross
            (canonicalValue G κ) s A B hClosed hBack
        have hStrong := G.closedSubset_strong_step s A B
          hOld hAB hDisj hCase hNo
        change G.toPredimension.IsStrong
          (s ∩ (oldStage κ k ∪ component κ k))
          (oldStage κ k ∪ component κ k) at hStrong
        rw [← oldStage_succ κ k] at hStrong
        exact hStrong
  have hFinal := hInd n (by omega)
  rw [oldStage_final κ] at hFinal
  simpa only [Finset.inter_univ] using hFinal

end FiniteC0
end BigHrushovski
