import BigHrushovski.C0CoordinateCoherentLocalOrders

/-!
# Increasing coordinate reassignments of finite pointed C₀ codes

In the manuscript an increasing map h:ω→ω acts on the auxiliary
coordinate model W by replacing each coordinate e(x) with h(e(x)).
Before constructing W we can verify this operation on its finite
literal codes, including every graph pair and unary incidence pair.

The action commutes with restriction to a finite coordinate subset.
It also preserves the exact assertion that the distinguished point
generates the whole support. Injectivity of h is essential: an
arbitrary map may identify distinct vertices and destroy the code.

This is a FINITE coding interface for the future T_h action. It
does not claim that W exists or that the return map ψ exists.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Apply an increasing coordinate map to both endpoints of a finite
adjacency or unary-value incidence. -/
def relabelPair (h : ℕ ↪o ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (h p.1, h p.2)

/-- Relabel the complete pointed code under an increasing injection,
preserving all vertices and all complete incidence matrices. -/
noncomputable def LiteralPointedCode.relabel
    (q : LiteralPointedCode) (h : ℕ ↪o ℕ) : LiteralPointedCode where
  support := q.support.image h
  point := h q.point
  point_mem := Finset.mem_image.mpr ⟨q.point, q.point_mem, rfl⟩
  adjacencyPairs := q.adjacencyPairs.image (relabelPair h)
  closurePairs := q.closurePairs.image (relabelPair h)

/-- Strictly increasing coordinates recover source membership of a
complete subset exactly. -/
theorem mem_orderEmbedding_image_iff
    (h : ℕ ↪o ℕ) (s : Finset ℕ) (x : ℕ) :
    h x ∈ s.image h ↔ x ∈ s := by
  classical
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    have hxy : y = x := h.injective heq
    simpa only [hxy] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

/-- Increasing coordinate relabelling neither adds nor removes an
ordered graph edge or nonedge among its relabelled vertices. -/
theorem mem_relabel_adj_iff
    (q : LiteralPointedCode) (h : ℕ ↪o ℕ)
    (u v : ℕ) :
    (h u,h v) ∈ (q.relabel h).adjacencyPairs ↔
      (u,v) ∈ q.adjacencyPairs := by
  classical
  constructor
  · intro hp
    obtain ⟨p,hp,hEq⟩ := Finset.mem_image.mp hp
    have hu : p.1 = u :=
      h.injective (congrArg Prod.fst hEq)
    have hv : p.2 = v :=
      h.injective (congrArg Prod.snd hEq)
    have hPair : p = (u, v) := Prod.ext hu hv
    rw [hPair] at hp
    exact hp
  · intro hp
    exact Finset.mem_image.mpr ⟨(u,v),hp,rfl⟩

/-- The same exact reflection holds for every element of every
complete unary value, not merely for its cardinality. -/
theorem mem_relabel_closure_iff
    (q : LiteralPointedCode) (h : ℕ ↪o ℕ)
    (u v : ℕ) :
    (h u,h v) ∈ (q.relabel h).closurePairs ↔
      (u,v) ∈ q.closurePairs := by
  classical
  constructor
  · intro hp
    obtain ⟨p,hp,hEq⟩ := Finset.mem_image.mp hp
    have hu : p.1 = u :=
      h.injective (congrArg Prod.fst hEq)
    have hv : p.2 = v :=
      h.injective (congrArg Prod.snd hEq)
    have hPair : p = (u, v) := Prod.ext hu hv
    rw [hPair] at hp
    exact hp
  · intro hp
    exact Finset.mem_image.mpr ⟨(u,v),hp,rfl⟩

/-- A finite incidence set restricted to a vertex subset can be
relabelled before or after restriction, with exactly the same result.
Injectivity is used in the reverse implication. -/
private theorem image_filter_pairs
    (T : Finset (ℕ × ℕ)) (s : Finset ℕ)
    (h : ℕ ↪o ℕ) :
    (T.filter (fun p : ℕ × ℕ =>
        p.1 ∈ s ∧ p.2 ∈ s)).image (relabelPair h) =
      (T.image (relabelPair h)).filter (fun p : ℕ × ℕ =>
        p.1 ∈ s.image h ∧ p.2 ∈ s.image h) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hp
    obtain ⟨hT,hs1,hs2⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨q,hT,hEq⟩, ?_⟩
    rw [← hEq]
    exact ⟨Finset.mem_image.mpr ⟨q.1,hs1,rfl⟩,
      Finset.mem_image.mpr ⟨q.2,hs2,rfl⟩⟩
  · intro hp
    obtain ⟨hIm,hs1,hs2⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hT,hEq⟩ := Finset.mem_image.mp hIm
    have hs1' : h q.1 ∈ s.image h := by
      simpa only [← hEq, relabelPair] using hs1
    have hs2' : h q.2 ∈ s.image h := by
      simpa only [← hEq, relabelPair] using hs2
    have hq1 : q.1 ∈ s := (mem_orderEmbedding_image_iff h s q.1).mp hs1'
    have hq2 : q.2 ∈ s := (mem_orderEmbedding_image_iff h s q.2).mp hs2'
    exact Finset.mem_image.mpr
      ⟨q, Finset.mem_filter.mpr ⟨hT,hq1,hq2⟩,hEq⟩

/-- The exact finite relabelling action commutes with pointed
restriction, even when the original distinguished point is not in
the smaller subset. All complete C and graph pairs are preserved. -/
theorem LiteralPointedCode.relabel_restrictTo
    (q : LiteralPointedCode) (h : ℕ ↪o ℕ)
    (s : Finset ℕ) (hs : s ⊆ q.support)
    (v : ℕ) (hv : v ∈ s) :
    (q.restrictTo s hs v hv).relabel h =
      (q.relabel h).restrictTo (s.image h)
        (by
          intro x hx
          obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image.mpr ⟨u,hs hu,rfl⟩)
        (h v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩) := by
  classical
  apply LiteralPointedCode.ext
  · rfl
  · rfl
  · exact image_filter_pairs q.adjacencyPairs s h
  · exact image_filter_pairs q.closurePairs s h

/-- The pointed vertex still generates exactly the whole support
after an increasing coordinate assignment. -/
theorem LiteralPointedCode.relabel_generated
    (q : LiteralPointedCode) (h : ℕ ↪o ℕ)
    (hq : q.IsGeneratedByPoint) :
    (q.relabel h).IsGeneratedByPoint := by
  classical
  intro y
  constructor
  · intro hy
    obtain ⟨v,hv,hEq⟩ := Finset.mem_image.mp hy
    have hPair : (q.point,v) ∈ q.closurePairs :=
      (hq v).mp hv
    apply Finset.mem_image.mpr
    refine ⟨(q.point,v),hPair,?_⟩
    change (h q.point,h v) = (h q.point,y)
    rw [hEq]
  · intro hPair
    obtain ⟨p,hp,hEq⟩ := Finset.mem_image.mp hPair
    have hRoot : p.1 = q.point :=
      h.injective (congrArg Prod.fst hEq)
    have hPairEq : p = (q.point, p.2) :=
      Prod.ext hRoot rfl
    have hPairMem : (q.point, p.2) ∈ q.closurePairs := by
      rw [hPairEq] at hp
      exact hp
    have hpSupport : p.2 ∈ q.support :=
      (hq p.2).mpr hPairMem
    have hLabel : h p.2 = y := congrArg Prod.snd hEq
    exact Finset.mem_image.mpr ⟨p.2,hpSupport,hLabel⟩

end FiniteUnaryCoordinates
end BigHrushovski
