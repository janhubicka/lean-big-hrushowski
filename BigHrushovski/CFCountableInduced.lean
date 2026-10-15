import BigHrushovski.CFCountableGraph

/-!
# No new edges between vertices of earlier C_F stages

The countable graph is defined using finite-stage edge witnesses.
To show that its finite stages are induced, take a witness at
another finite stage and move both representations to a common
later stage. The birth labels then agree, so injectivity of
the stage-to-birth map identifies their finite representatives.
Inducedness of every iterated old embedding reflects the edge
back to the original stage.

This is a necessary separation: constructing a countable GraphOn
from witnessed edges did not by itself rule out new edges
between two vertices already present in an earlier finite stage.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Equality of level indices transports both endpoints of the
same finite graph without changing its adjacency. This explicit
transport lemma avoids relying on simplification of dependent casts. -/
private theorem graph_adj_cast (F : ℕ → ℝ) (K : ℕ → ℕ)
    {i j : ℕ} (h : i = j)
    (a b : (stage F K i).carrier) :
    (stage F K j).graph.adj
      (cast (congrArg (fun t => (stage F K t).carrier) h) a)
      (cast (congrArg (fun t => (stage F K t).carrier) h) b) ↔
        (stage F K i).graph.adj a b := by
  cases h
  rfl

/-- Equality of level indices likewise preserves the canonical
birth label of an old vertex. -/
private theorem toVertex_cast (F : ℕ → ℝ) (K : ℕ → ℕ)
    {i j : ℕ} (h : i = j)
    (a : (stage F K i).carrier) :
    toVertex F K j
        (cast (congrArg (fun t => (stage F K t).carrier) h) a) =
      toVertex F K i a := by
  cases h
  rfl

/-- The canonical iterated old embedding from stage n to a
later stage m, using explicit transport of the carrier type. -/
noncomputable def embedToLater (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ) (hnm : n ≤ m)
    (a : (stage F K n).carrier) : (stage F K m).carrier :=
  cast (congrArg (fun t => (stage F K t).carrier)
    (Nat.add_sub_of_le hnm))
    (ascend F K n (m - n) a)

/-- Iterated inducedness is unchanged by the dependent index cast
used to describe a later stage by its absolute level number. -/
theorem embedToLater_induced (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ) (hnm : n ≤ m)
    (a b : (stage F K n).carrier) :
    (stage F K m).graph.adj
      (embedToLater F K n m hnm a)
      (embedToLater F K n m hnm b) ↔
      (stage F K n).graph.adj a b := by
  unfold embedToLater
  exact (graph_adj_cast F K (Nat.add_sub_of_le hnm)
    (ascend F K n (m - n) a)
    (ascend F K n (m - n) b)).trans
      (ascend_induced F K n (m - n) a b)

/-- Birth labels are preserved by the same dependent transport. -/
theorem toVertex_embedToLater (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ) (hnm : n ≤ m)
    (a : (stage F K n).carrier) :
    toVertex F K m (embedToLater F K n m hnm a) =
      toVertex F K n a := by
  unfold embedToLater
  exact (toVertex_cast F K (Nat.add_sub_of_le hnm)
    (ascend F K n (m - n) a)).trans
      (toVertex_ascend F K n (m - n) a)

/-- Equal birth-labelled vertices represented in different
finite stages have equal images in any common later stage. -/
theorem same_birth_in_common_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m L : ℕ) (hn : n ≤ L) (hm : m ≤ L)
    (a : (stage F K n).carrier)
    (b : (stage F K m).carrier)
    (hBirth : toVertex F K n a = toVertex F K m b) :
    embedToLater F K n L hn a =
      embedToLater F K m L hm b := by
  apply toVertex_injective F K L
  calc
    toVertex F K L (embedToLater F K n L hn a)
        = toVertex F K n a :=
            toVertex_embedToLater F K n L hn a
    _ = toVertex F K m b := hBirth
    _ = toVertex F K L (embedToLater F K m L hm b) :=
            (toVertex_embedToLater F K m L hm b).symm

/-- Every canonical finite stage is an *induced* subgraph of
the countable birth-labelled graph. This verifies reflection of
nonedges, not only preservation of edges. -/
theorem countableGraph_stage_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (a b : (stage F K n).carrier) :
    (countableGraph F K).adj
      (toVertex F K n a) (toVertex F K n b) ↔
        (stage F K n).graph.adj a b := by
  constructor
  · intro h
    obtain ⟨m, c, d, hc, hd, hcd⟩ := h
    let L := max n m
    have hn : n ≤ L := Nat.le_max_left n m
    have hm : m ≤ L := Nat.le_max_right n m
    have hAC : embedToLater F K n L hn a =
        embedToLater F K m L hm c :=
      same_birth_in_common_stage F K n m L hn hm a c hc.symm
    have hBD : embedToLater F K n L hn b =
        embedToLater F K m L hm d :=
      same_birth_in_common_stage F K n m L hn hm b d hd.symm
    have hLater : (stage F K L).graph.adj
        (embedToLater F K n L hn a)
        (embedToLater F K n L hn b) := by
      rw [hAC, hBD]
      exact (embedToLater_induced F K m L hm c d).mpr hcd
    exact (embedToLater_induced F K n L hn a b).mp hLater
  · exact stage_edge_in_countableGraph F K n a b

end CFCoherentTower
end BigHrushovski
