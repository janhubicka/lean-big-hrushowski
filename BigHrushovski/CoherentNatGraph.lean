import BigHrushovski.StrongChain
import BigHrushovski.InfiniteGraph

/-!
# A graph obtained from coherent finite stages on ℕ

Each stage carries a finite set of Nat vertices and an ambient graph
predicate supported on that set. Old-old edges and nonedges are preserved
exactly at every successor stage. Together with monotone domains, these
hypotheses give a well-defined graph as the union of the stage relations.

This isolates the graph-coherence step of the strong Fraïssé construction.
The stage system and its growth, strongness, and fair-response properties
must subsequently be constructed, not postulated as consequences.
-/

namespace BigHrushovski

/-- Coherent stages of a graph construction on the common Nat carrier.
The cover field is explicit: increasing finite supports alone do not
guarantee that every natural number occurs in a stage. -/
structure CoherentNatGraphStages where
  stage : ℕ → Finset ℕ
  graph : ℕ → GraphOn ℕ
  stage_step : ∀ n, stage n ⊆ stage (n + 1)
  edge_support : ∀ n x y,
    (graph n).adj x y → x ∈ stage n ∧ y ∈ stage n
  agrees_old : ∀ n x y,
    x ∈ stage n → y ∈ stage n →
    ((graph n).adj x y ↔ (graph (n + 1)).adj x y)
  covers : ∀ x : ℕ, ∃ n, x ∈ stage n

namespace CoherentNatGraphStages

variable (S : CoherentNatGraphStages)

/-- The finite domains are monotone at arbitrary pairs of stages. -/
theorem stage_mono {n m : ℕ} (hnm : n ≤ m) :
    S.stage n ⊆ S.stage m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      intro x hx
      exact hx
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact (ih hle).trans (S.stage_step m)
      · have hn : n = m + 1 := by omega
        subst n
        intro x hx
        exact hx

/-- Every pair of old vertices has the same adjacency at any later stage.
Both directions matter: preserving only edges would allow new edges
between previously nonadjacent old vertices. -/
theorem agrees_of_le {n m : ℕ} (hnm : n ≤ m)
    {x y : ℕ} (hx : x ∈ S.stage n) (hy : y ∈ S.stage n) :
    (S.graph n).adj x y ↔ (S.graph m).adj x y := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      by_cases hle : n ≤ m
      · have hxM : x ∈ S.stage m := S.stage_mono hle hx
        have hyM : y ∈ S.stage m := S.stage_mono hle hy
        exact (ih hle).trans (S.agrees_old m x y hxM hyM)
      · have hn : n = m + 1 := by omega
        subst n
        rfl

/-- Edges can only persist, because each edge lies in the finite support
and exact old-old agreement holds across the stages. -/
theorem edge_mono {n m : ℕ} (hnm : n ≤ m)
    {x y : ℕ} (hAdj : (S.graph n).adj x y) :
    (S.graph m).adj x y := by
  have hxy := S.edge_support n x y hAdj
  exact (S.agrees_of_le hnm hxy.1 hxy.2).mp hAdj

/-- The direct-limit graph has an edge exactly when some stage has it. -/
def limitGraph : GraphOn ℕ where
  adj x y := ∃ n, (S.graph n).adj x y
  symm := by
    intro x y h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, (S.graph n).symm x y hn⟩
  irrefl := by
    intro x h
    obtain ⟨n, hn⟩ := h
    exact (S.graph n).irrefl x hn

/-- Every finite stage is an induced subgraph of the direct limit, in
both directions, including the reflection of all old nonedges. -/
theorem limitGraph_induced (n : ℕ) {x y : ℕ}
    (hx : x ∈ S.stage n) (hy : y ∈ S.stage n) :
    S.limitGraph.adj x y ↔ (S.graph n).adj x y := by
  constructor
  · rintro ⟨m, hm⟩
    have hBig : (S.graph (max n m)).adj x y :=
      S.edge_mono (Nat.le_max_right n m) hm
    exact (S.agrees_of_le (Nat.le_max_left n m) hx hy).mpr hBig
  · intro h
    exact ⟨n, h⟩

end CoherentNatGraphStages
end BigHrushovski
