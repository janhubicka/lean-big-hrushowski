import BigHrushovski.GrowingFiniteResponse
import BigHrushovski.ApplicableFiniteStage
import BigHrushovski.CanonicalFinNumbering
import BigHrushovski.InitialSegmentGraphStage

/-!
# A growing Nat-labelled response to an applicable finite request

Suppose a finite two-sparse graph stage is carried by the consecutive
natural-number interval `range n`. If a labelled finite strong
extension request applies to this stage, it can be answered while
passing to a *strictly larger* initial segment.

The construction first pulls the source map back to `Fin n`,
performs finite strong amalgamation followed by forced growth,
and then labels the resulting finite carrier by the consecutive
numbers using the canonical old numbering of `Fin n`.

The output keeps all old labels and induced old-old nonedges, is
two-sparse and supported on its finite interval, has the old interval
strong, and contains a strong induced response extending the original
Nat-labelled source map pointwise.

This is one successor step; the countable recursion remains to be
constructed separately.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- An applicable finite strong request has a strictly growing
successor stage supported on a gap-free Nat interval. -/
theorem exists_growing_nat_response
    (G : GraphOn ℕ) (n : ℕ)
    (hSparse : G.IsTwoSparse (Finset.range n))
    (req : ExtensionRequestCatalogue)
    (hApplies : AppliesAt G (Finset.range n) req) :
    ∃ (m : ℕ) (N : GraphOn ℕ),
      n < m ∧
      N.IsTwoSparse (Finset.range m) ∧
      (∀ x y : ℕ, N.adj x y →
        x ∈ Finset.range m ∧ y ∈ Finset.range m) ∧
      (∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n,
        G.adj x y ↔ N.adj x y) ∧
      N.toPredimension.IsStrong (Finset.range n) (Finset.range m) ∧
      RespondsAt N (Finset.range m) req := by
  classical
  obtain ⟨f, hf, hVal, hSourceAdj, hSparseFin, hStrongFin⟩ :=
    exists_finite_applicable_source G n hSparse req hApplies
  let A : GraphOn (Fin n) :=
    G.pullback (fun z : Fin n => z.val)
  let diagram := req.2.2.1
  obtain ⟨K, old, answer, fresh, hOldInj, hAnswerInj,
      hOldAdj, hAnswerAdj, hBase, _, hSparseK,
      hStrongOld, hStrongAnswer, hFresh⟩ :=
    exists_growing_finite_strong_response
      A hSparseFin diagram f hf hSourceAdj hStrongFin
  obtain ⟨new, N, hFixed, hTransport, hSparseN,
      hStrongN, hSupportN⟩ :=
    FiniteSpan.exists_initial_segment_strong_nat_stage
      K old hOldInj hStrongOld hSparseK
      (FiniteSpan.canonicalFinNumbering n)
  let B := GrowingResponseCarrier f diagram
  let m := Fintype.card B

  have hOldNumeric (x : Fin n) :
      (new (old x)).val = x.val := by
    calc
      (new (old x)).val =
          (FiniteSpan.canonicalFinNumbering n x).val := hFixed x
      _ = x.val := FiniteSpan.canonicalFinNumbering_val n x

  have hFreshAbove : n ≤ (new fresh).val := by
    by_contra hn
    have hSmall : (new fresh).val < n := Nat.lt_of_not_ge hn
    let x : Fin n := ⟨(new fresh).val, hSmall⟩
    have hEq : new (old x) = new fresh := by
      apply Fin.ext
      change (new (old x)).val = (new fresh).val
      rw [hOldNumeric x]
    have hOldEq : old x = fresh := new.injective hEq
    exact hFresh (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, hOldEq⟩)
  have hGrowth : n < m :=
    lt_of_le_of_lt hFreshAbove (new fresh).isLt

  have hAgreeOld :
      ∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n,
        G.adj x y ↔ N.adj x y := by
    intro x hx y hy
    let a : Fin n := ⟨x, Finset.mem_range.mp hx⟩
    let b : Fin n := ⟨y, Finset.mem_range.mp hy⟩
    have hLink :
        G.adj a.val b.val ↔
          N.adj (new (old a)).val (new (old b)).val :=
      (hOldAdj a b).symm.trans (hTransport (old a) (old b))
    simpa only [hOldNumeric a, hOldNumeric b] using hLink

  have hStrongNat :
      N.toPredimension.IsStrong
        (Finset.range n) (Finset.range m) := by
    simpa only [Fintype.card_fin] using hStrongN

  let label : B → ℕ := fun b => (new b).val
  let reply : Fin req.2.1 → ℕ := label ∘ answer
  have hLabelInj : Function.Injective label := by
    intro x y h
    exact new.injective (Fin.ext h)
  have hReplyInj : Function.Injective reply :=
    hLabelInj.comp hAnswerInj
  have hReplyAdj :
      ∀ x y : Fin req.2.1,
        diagram.target.adj x y ↔ N.adj (reply x) (reply y) := by
    intro x y
    exact (hAnswerAdj x y).symm.trans
      (hTransport (answer x) (answer y))
  have hReplyBase :
      ∀ x : Fin req.1,
        reply (diagram.embedding x) = req.2.2.2 x := by
    intro x
    calc
      reply (diagram.embedding x) =
          (new (answer (diagram.embedding x))).val := rfl
      _ = (new (old (f x))).val :=
          congrArg (fun z => (new z).val) (hBase x).symm
      _ = (f x).val := hOldNumeric (f x)
      _ = req.2.2.2 x := hVal x
  have hFullImage :
      (Finset.univ : Finset B).image label = Finset.range m := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨b, hb⟩
      rw [← hb]
      exact (new b).isLt
    · intro hx
      refine ⟨new.symm ⟨x, hx⟩, ?_⟩
      simp [label]
  have hReplyImage :
      (((Finset.univ : Finset (Fin req.2.1)).image answer).image label) =
      (Finset.univ : Finset (Fin req.2.1)).image reply := by
    simp only [Finset.image_image, reply]
  have hStrongReplyNat :
      N.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin req.2.1)).image reply)
        (Finset.range m) := by
    have h :=
      (K.strong_image_iff N label hLabelInj
        (fun x y => hTransport x y)
        ((Finset.univ : Finset (Fin req.2.1)).image answer)
        (Finset.univ : Finset B)
        (Finset.subset_univ _)).mpr hStrongAnswer
    rw [hReplyImage, hFullImage] at h
    exact h
  have hRespond : RespondsAt N (Finset.range m) req :=
    ⟨reply, hReplyInj, hReplyAdj, hReplyBase, hStrongReplyNat⟩
  exact ⟨m, N, hGrowth, hSparseN, hSupportN,
    hAgreeOld, hStrongNat, hRespond⟩

end FiniteCatalogue
end BigHrushovski
