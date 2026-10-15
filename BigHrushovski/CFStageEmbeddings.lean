import BigHrushovski.CFBirthCarrier

/-!
# Coherence of all finite C_F stage embeddings

A one-step tagged construction carries the old part by Sum.inl.
Its iterates are the canonical maps from stage n to stage n+k.
This module checks their injection, full inducedness (both edges
and nonedges), and compatibility with birth-labelled vertices.

No canonical arbitrary renumbering or quotient of finite stages
is introduced. These results will let a graph on the countable
birth carrier be defined by an edge witnessed at a finite stage,
and will be used to show independence of that witness.

The strict d-closedness of the image at arbitrary later stages
is isolated as a separate proof obligation; one-step strictness
is already certified in CFCoherentStages.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Canonical old-vertex embedding k levels beyond stage n.
At every step this is literally Sum.inl. -/
noncomputable def ascend (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    (k : ℕ) → (stage F K n).carrier →
      (stage F K (n + k)).carrier
  | 0 => id
  | k + 1 => fun x => Sum.inl (ascend F K n k x)

/-- Every iterated old-stage map is injective. -/
theorem ascend_injective (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) : Function.Injective (ascend F K n k) := by
  induction k with
  | zero =>
      intro a b h
      exact h
  | succ k ih =>
      intro a b h
      exact ih (Sum.inl.inj h)

/-- The complete adjacency relation is preserved and reflected
across every finite number of successor stages. -/
theorem ascend_induced (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) (a b : (stage F K n).carrier) :
    (stage F K (n + k)).graph.adj
      (ascend F K n k a) (ascend F K n k b) ↔
      (stage F K n).graph.adj a b := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      have hStep := stage_succ_induced F K (n + k)
        (ascend F K n k a) (ascend F K n k b)
      exact hStep.trans ih

/-- The birth label of an old vertex is unchanged by *any*
finite number of later old-stage inclusions. -/
theorem toVertex_ascend (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) (a : (stage F K n).carrier) :
    toVertex F K (n + k) (ascend F K n k a) =
      toVertex F K n a := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      exact (toVertex_old F K (n + k)
        (ascend F K n k a)).trans ih

/-- Compatibility of iterated embeddings with the canonical
countable carrier makes equal birth labels agree after a
common finite extension, rather than identifying vertices
by a freely chosen isomorphism. -/
theorem toVertex_ascend_injective (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) (a b : (stage F K n).carrier)
    (h : toVertex F K (n + k) (ascend F K n k a) =
      toVertex F K (n + k) (ascend F K n k b)) :
    a = b := by
  exact (toVertex_injective F K n)
    ((toVertex_ascend F K n k a).symm.trans
      (h.trans (toVertex_ascend F K n k b)))

end CFCoherentTower
end BigHrushovski
