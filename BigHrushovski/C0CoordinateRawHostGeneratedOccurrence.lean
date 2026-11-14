import BigHrushovski.C0CoordinateRawHostBoundedFibres
import BigHrushovski.C0CoordinateRawHostFiniteOccurrence

/-!
# Exact finite generated occurrences inside the raw C₀ coordinate host

For a finite canonical C₀ presentation p, let C(a) be the complete
one-generated closure of a. The already constructed map sending a
vertex b to its complete pointed coordinate code is injective and
preserves and reflects the graph and the named unary values C and J.

Here we restrict this map to C(a) and obtain a literal equivalence
with the finite raw-host unary value of the code of a. This is the
correct finite occurrence lemma to reuse in a future proof that every
finite closed raw-host substructure is in the finite functional age.

The equivalence remembers complete graph and unary data. It does
not assume that a globally coherent catalogue of ordered local
representatives has been chosen, and it is not the countable return
embedding of manuscript section 4.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The complete generated closure of a finite canonical C₀ vertex
is in bijection with the full raw-host unary C-value of its pointed
coordinate code. No unpointed quotient or root-selection ambiguity
remains. -/
noncomputable def FiniteChronologicalC0.generatedOccurrenceEquiv
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (FiniteC0.canonicalValue p.graph p.component a) ≃
      (p.asRawVertex e a).closedValue := by
  classical
  let S := FiniteC0.canonicalValue p.graph p.component a
  let f : S → (p.asRawVertex e a).closedValue := fun b =>
    ⟨p.asRawVertex e b.val,
      (p.asRawVertex_mem_closedValue_iff e a b.val).mpr b.property⟩
  have hf : Function.Injective f := by
    intro b c h
    have hCodes : p.asRawVertex e b.val =
        p.asRawVertex e c.val :=
      congrArg Subtype.val h
    exact Subtype.ext (p.asRawVertex_injective e hCodes)
  have hsurj : Function.Surjective f := by
    intro r
    obtain ⟨b,hb,hEq⟩ :=
      (p.mem_asRawVertex_closedValue_iff e a r.val).mp r.property
    refine ⟨⟨b,hb⟩, ?_⟩
    apply Subtype.ext
    exact hEq.symm
  exact Equiv.ofBijective f ⟨hf,hsurj⟩

/-- The equivalence sends a vertex of C(a) to its entire pointed
finite code in the raw host. It does not replace the code by its
distinguished coordinate. -/
theorem FiniteChronologicalC0.generatedOccurrenceEquiv_apply
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m)
    (b : FiniteC0.canonicalValue p.graph p.component a) :
    (p.generatedOccurrenceEquiv e a b).val =
      p.asRawVertex e b.val := rfl

/-- The exact finite graph, including nonedges, is reflected under
the generated-occurrence equivalence. -/
theorem FiniteChronologicalC0.generatedOccurrence_graph_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m)
    (u v : FiniteC0.canonicalValue p.graph p.component a) :
    rawC0HostGraph.adj (p.generatedOccurrenceEquiv e a u).val
      (p.generatedOccurrenceEquiv e a v).val ↔
        p.graph.adj u.val v.val := by
  change rawC0HostGraph.adj (p.asRawVertex e u.val)
    (p.asRawVertex e v.val) ↔ p.graph.adj u.val v.val
  exact p.asRawVertex_graph_adj_iff e u.val v.val

/-- Exact reflection of every complete unary C-incidence between
vertices of the generated closure. Both directions are required. -/
theorem FiniteChronologicalC0.generatedOccurrence_C_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m)
    (u v : FiniteC0.canonicalValue p.graph p.component a) :
    (p.generatedOccurrenceEquiv e a v).val ∈
        (p.generatedOccurrenceEquiv e a u).val.closedValue ↔
      v.val ∈ FiniteC0.canonicalValue p.graph p.component u.val := by
  change p.asRawVertex e v.val ∈
      (p.asRawVertex e u.val).closedValue ↔ _
  exact p.asRawVertex_mem_closedValue_iff e u.val v.val

/-- Exact reflection of the named back-neighbour J relation
inside the complete generated closure. -/
theorem FiniteChronologicalC0.generatedOccurrence_J_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m)
    (u v : FiniteC0.canonicalValue p.graph p.component a) :
    (p.generatedOccurrenceEquiv e a v).val ∈
        (p.generatedOccurrenceEquiv e a u).val.backNeighbours ↔
      v.val ∈ FiniteC0.canonicalValue p.graph p.component u.val ∧
        p.graph.adj u.val v.val := by
  change p.asRawVertex e v.val ∈
      (p.asRawVertex e u.val).backNeighbours ↔ _
  exact p.asRawVertex_backNeighbours_iff e u.val v.val

/-- Package the three complete finite-language equivalences
for any one-generated C₀ closure and its actual raw host occurrence. -/
theorem FiniteChronologicalC0.generatedOccurrence_exact
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (∀ u v : FiniteC0.canonicalValue p.graph p.component a,
      rawC0HostGraph.adj (p.generatedOccurrenceEquiv e a u).val
        (p.generatedOccurrenceEquiv e a v).val ↔
          p.graph.adj u.val v.val) ∧
    (∀ u v : FiniteC0.canonicalValue p.graph p.component a,
      (p.generatedOccurrenceEquiv e a v).val ∈
        (p.generatedOccurrenceEquiv e a u).val.closedValue ↔
          v.val ∈ FiniteC0.canonicalValue p.graph p.component u.val) ∧
    (∀ u v : FiniteC0.canonicalValue p.graph p.component a,
      (p.generatedOccurrenceEquiv e a v).val ∈
        (p.generatedOccurrenceEquiv e a u).val.backNeighbours ↔
          v.val ∈ FiniteC0.canonicalValue p.graph p.component u.val ∧
            p.graph.adj u.val v.val) := by
  exact ⟨p.generatedOccurrence_graph_iff e a,
    p.generatedOccurrence_C_iff e a,
    p.generatedOccurrence_J_iff e a⟩

end FiniteUnaryCoordinates
end BigHrushovski
