import BigHrushovski.C0FunctionalFiniteInitialLabels
import BigHrushovski.CanonicalFinNumbering
import BigHrushovski.InducedEmbedding

/-!
# A prescribed finite functional C₀ request on consecutive coordinates

The finite tagged responding theorem returns a canonical
component-indexed graph on a nested finite tagged carrier. We
now use the old-fixed initial-segment equivalence to transport
this response to Fin(card carrier). Both original graph maps are
induced and strong, every complete unary value of both factors
is transported exactly, and each old numerical coordinate is
fixed pointwise.

No countable chain or response schedule is assumed. This is the
finite successor interface needed for the later fair recursion.
A strictly growing successor requires a separate forced-growth
operation when a request contributes no new vertices.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every applicable finite functional diagram admits an actual
finite ordinal response. The old finite stage embeds by a map
which fixes *numerical coordinates* and the requested target
embeds over its original source map. The complete canonical
unary function, including all recursively backward-reachable
components, is preserved on both factors. Both images are
strong in the new finite graph.

The target size may equal the old size if all request vertices
are already present; forced growth is a separate finite step. -/
theorem exists_finiteOrdinalFunctionalResponse
    {a p b q c r : ℕ}
    (S : FiniteFunctionalC0 a p)
    (D : FunctionalC0Diagram b q c r)
    (e : Fin b → Fin a)
    (he : Function.Injective e)
    (hInd : ∀ x y : Fin b,
      D.source.graph.adj x y ↔ S.graph.adj (e x) (e y))
    (hValues : ∀ x : Fin b,
      S.unaryValue (e x) =
        (D.source.unaryValue x).image e) :
    ∃ (size t : ℕ)
      (M : FiniteFunctionalC0 size t)
      (old : Fin a → Fin size)
      (target : Fin c → Fin size),
      Function.Injective old ∧
      Function.Injective target ∧
      (∀ x : Fin a, (old x).val = x.val) ∧
      (∀ x y : Fin a,
        S.graph.adj x y ↔ M.graph.adj (old x) (old y)) ∧
      (∀ x y : Fin c,
        D.target.graph.adj x y ↔
          M.graph.adj (target x) (target y)) ∧
      (∀ x : Fin a,
        M.unaryValue (old x) =
          (S.unaryValue x).image old) ∧
      (∀ x : Fin c,
        M.unaryValue (target x) =
          (D.target.unaryValue x).image target) ∧
      (∀ x : Fin b, old (e x) = target (D.embedding x)) ∧
      M.graph.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin a)).image old)
        Finset.univ ∧
      M.graph.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin c)).image target)
        Finset.univ := by
  classical
  let W : Type := TaggedAmalgam.Carrier (Fin b)
    (FiniteSpan.Tail e) (FiniteSpan.Tail D.embedding)
  let L := FiniteSpan.normalGraph S.graph e he
  let R := FiniteSpan.normalGraph D.target.graph
    D.embedding D.inj
  let K : GraphOn W := TaggedAmalgam.freeGraph L R
  let f : Fin a → W :=
    FiniteSpan.leftAmalgamEmbedding e he D.embedding
  let g : Fin c → W :=
    FiniteSpan.rightAmalgamEmbedding e D.embedding D.inj
  have hf : Function.Injective f :=
    FiniteSpan.leftAmalgamEmbedding_injective e he D.embedding
  have hg : Function.Injective g :=
    FiniteSpan.rightAmalgamEmbedding_injective e D.embedding D.inj
  obtain ⟨t, κ, hSparse, hStrongL, hStrongR,
      hSteps, hAdjL, hAdjR, hValuesL, hValuesR, hBase⟩ :=
    exists_taggedResponse_to_functionalC0Request
      S D e he hInd hValues
  have hOldValues : ∀ x : Fin a,
      FiniteC0.canonicalValue K κ (f x) =
        (FiniteC0.canonicalValue S.graph S.index x).image f :=
    hValuesL
  obtain ⟨M, label, hFixed, hAdjLabel, hValLabel, hOldVal⟩ :=
    exists_initialSegment_canonicalFunctionalExtension
      S.graph K S.index κ hSteps f hf
      (FiniteSpan.canonicalFinNumbering a) hOldValues
  let old : Fin a → Fin (Fintype.card W) := label ∘ f
  let target : Fin c → Fin (Fintype.card W) := label ∘ g
  have hFullOld : ∀ x : Fin a,
      M.unaryValue (old x) = (S.unaryValue x).image old := by
    intro x
    change M.unaryValue (label (f x)) =
      (S.unaryValue x).image (label ∘ f)
    exact hOldVal x
  have hFullTarget : ∀ x : Fin c,
      M.unaryValue (target x) =
        (D.target.unaryValue x).image target := by
    intro x
    calc
      M.unaryValue (target x) =
        (FiniteC0.canonicalValue K κ (g x)).image label :=
          hValLabel (g x)
      _ = ((D.target.unaryValue x).image g).image label := by
        rw [hValuesR x]
      _ = (D.target.unaryValue x).image target := by
        rw [Finset.image_image]
        rfl
  have hKToM : ∀ x y : W,
      K.adj x y ↔ M.graph.adj (label x) (label y) := hAdjLabel
  have hOldStrongK : K.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin a)).image f)
      (Finset.univ : Finset W) := by
    rw [FiniteSpan.leftAmalgamEmbedding_image_univ
      e he D.embedding]
    exact hStrongL
  have hTargetStrongK : K.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin c)).image g)
      (Finset.univ : Finset W) := by
    rw [FiniteSpan.rightAmalgamEmbedding_image_univ
      e D.embedding D.inj]
    exact hStrongR
  have hLabUniv :
      (Finset.univ : Finset W).image label =
        (Finset.univ : Finset (Fin (Fintype.card W))) :=
    Finset.image_univ_of_surjective label.surjective
  have hOldStrongM : M.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin a)).image old)
      (Finset.univ : Finset (Fin (Fintype.card W))) := by
    have h :=
      (K.strong_image_iff M.graph label label.injective
        hKToM ((Finset.univ : Finset (Fin a)).image f)
        Finset.univ (Finset.subset_univ _)).mpr hOldStrongK
    rw [Finset.image_image, hLabUniv] at h
    exact h
  have hTargetStrongM : M.graph.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin c)).image target)
      (Finset.univ : Finset (Fin (Fintype.card W))) := by
    have h :=
      (K.strong_image_iff M.graph label label.injective
        hKToM ((Finset.univ : Finset (Fin c)).image g)
        Finset.univ (Finset.subset_univ _)).mpr hTargetStrongK
    rw [Finset.image_image, hLabUniv] at h
    exact h
  refine ⟨Fintype.card W, t, M, old, target,
    label.injective.comp hf, label.injective.comp hg,
    ?_, ?_, ?_, hFullOld, hFullTarget, ?_,
    hOldStrongM, hTargetStrongM⟩
  · intro x
    change (label (f x)).val = x.val
    calc
      (label (f x)).val =
        (FiniteSpan.canonicalFinNumbering a x).val := hFixed x
      _ = x.val := FiniteSpan.canonicalFinNumbering_val a x
  · intro x y
    exact (hAdjL x y).trans (hKToM (f x) (f y))
  · intro x y
    exact (hAdjR x y).trans (hKToM (g x) (g y))
  · intro x
    change label (f (e x)) = label (g (D.embedding x))
    exact congrArg label (hBase x)

end FiniteCatalogue
end BigHrushovski
