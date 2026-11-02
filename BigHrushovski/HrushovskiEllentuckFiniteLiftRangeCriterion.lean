import BigHrushovski.HrushovskiEllentuckCFRangeForward

/-!
# Finite lifting criterion for the full level-support range formula

The backward inclusion in the manuscript's range equation is not a
consequence of complete closure preservation alone. It follows from a
finite inverse level-assignment theorem together with uniqueness of
finite functional embeddings determined by their level assignments.

We state the exact requirements in terms of a predicate on embeddings
of the finite generated-closed set Γ(v). In each concrete application this
predicate must mean genuine ordered functional embedding, including
all complete function values. No theorem here asserts these
requirements for the C_F construction: they are Track B obligations.
-/

namespace BigHrushovski.Ellentuck

universe u v

variable {Vertex : Type u} {Level : Type v}

/-- A finite source domain with its original vertex names. -/
abbrev FiniteDomain (s : Finset Vertex) : Type u :=
  {x : Vertex // x ∈ s}

/-- The finite existence/uniqueness argument yields the *full* range
formula. Unlike the forward inclusion, its converse explicitly assumes
the existence of inverse level assignments as finite genuine
embeddings, and uniqueness of such embeddings at each level map.

The requirements are intentionally separated:
* inclusion of a finite closed set is an embedding;
* composing a finite embedding with the given global map f is an
  embedding;
* two finite embeddings agreeing on every output level coincide;
* for a complete support contained in range(h), there is a finite
  embedding with the prescribed inverse level assignment.
-/
theorem range_eq_supportDomain_of_finite_lifts
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (f : Vertex → Vertex) (h : Level → Level)
    (hSelf : ∀ v : Vertex, v ∈ Γ v)
    (hClosure : ∀ v, (Γ v).image f = Γ (f v))
    (hLevel : ∀ v, π (f v) = h (π v))
    (FiniteEmbedding : (s : Finset Vertex) →
      (FiniteDomain s → Vertex) → Prop)
    (hInclusion : ∀ v, FiniteEmbedding (Γ v) (fun x => x.1))
    (hCompose : ∀ v (g : FiniteDomain (Γ v) → Vertex),
      FiniteEmbedding (Γ v) g →
        FiniteEmbedding (Γ v) (fun x => f (g x)))
    (hUnique : ∀ v (g k : FiniteDomain (Γ v) → Vertex),
      FiniteEmbedding (Γ v) g →
      FiniteEmbedding (Γ v) k →
      (∀ x : FiniteDomain (Γ v), π (g x) = π (k x)) →
      g = k)
    (hInverseLift : ∀ v : Vertex,
      (∀ q ∈ generatedSupport Γ π v, q ∈ Set.range h) →
      ∃ g : FiniteDomain (Γ v) → Vertex,
        FiniteEmbedding (Γ v) g ∧
        (∀ x : FiniteDomain (Γ v),
          h (π (g x)) = π x.1)) :
    (Set.range f : Set Vertex) =
      supportDomain (generatedSupport Γ π) (Set.range h) := by
  apply Set.Subset.antisymm
  · exact image_subset_supportDomain Γ π f h hClosure hLevel
  · intro v hv
    obtain ⟨g, hgEmb, hgLevel⟩ := hInverseLift v hv
    have hfgEmb : FiniteEmbedding (Γ v) (fun x => f (g x)) :=
      hCompose v g hgEmb
    have hinclEmb : FiniteEmbedding (Γ v) (fun x => x.1) :=
      hInclusion v
    have hlevels :
        ∀ x : FiniteDomain (Γ v),
          π (f (g x)) = π x.1 := by
      intro x
      calc
        π (f (g x)) = h (π (g x)) := hLevel (g x)
        _ = π x.1 := hgLevel x
    have hsame :
        (fun x : FiniteDomain (Γ v) => f (g x)) =
          (fun x : FiniteDomain (Γ v) => x.1) :=
      hUnique v (fun x => f (g x)) (fun x => x.1)
        hfgEmb hinclEmb hlevels
    refine ⟨g ⟨v, hSelf v⟩, ?_⟩
    exact congrFun hsame ⟨v, hSelf v⟩

end BigHrushovski.Ellentuck
