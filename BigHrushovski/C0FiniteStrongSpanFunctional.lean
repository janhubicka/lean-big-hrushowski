import BigHrushovski.C0FiniteEquivTransport
import BigHrushovski.C0FiniteGraphLift

/-!
# Functional C0 lifting of arbitrary finite strong graph spans

Let A embed as a strong induced graph in two finite 2-sparse graphs
C and B. Suppose C carries its prescribed canonical finite C0
component indexing and complete set-valued unary closure.

Take the already certified tagged strong graph free amalgam
D = C ⊕_A B, with induced strong embeddings f:C→D and g:B→D
identifying exactly the common base A. The canonical old-index
transport lemma puts the functional presentation on the literal
image f[C], and the finite literal-strong lifting theorem extends
it to D. In particular, every complete original unary value
is exactly preserved under f.

This is the finite graph-to-functional lifting statement needed to
show that the graph reduct of the functional Fraïssé limit has the
strong extension property. The countable limit and its extension
property remain a distinct final step.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {P C B : Type*}
variable [Fintype P] [Fintype C] [Fintype B]
variable [DecidableEq P] [DecidableEq C] [DecidableEq B]
variable {n : ℕ}

/-- Given arbitrary strong embeddings of a common finite graph base
into the old canonical functional structure C and a finite strong
graph extension B, construct a tagged 2-sparse graph K with strong
induced factor embeddings and a canonical finite C0 functional
presentation extending the old *named* set-valued unary values
exactly through the old induced embedding. -/
theorem exists_canonical_functional_strong_amalgam
    (G : GraphOn C) (H : GraphOn B)
    (i : P → C) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset C))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i) (Finset.univ : Finset C))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j) (Finset.univ : Finset B))
    (κ : C → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κ k = FiniteC0.oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k) (FiniteC0.oldStage κ (k+1))) :
    ∃ (K : GraphOn (TaggedAmalgam.Carrier P (Tail i) (Tail j)))
      (f : C → TaggedAmalgam.Carrier P (Tail i) (Tail j))
      (g : B → TaggedAmalgam.Carrier P (Tail i) (Tail j))
      (m : ℕ)
      (κFinal : TaggedAmalgam.Carrier P (Tail i) (Tail j) → Fin m),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ x y : C, G.adj x y ↔ K.adj (f x) (f y)) ∧
      (∀ x y : B, H.adj x y ↔ K.adj (g x) (g y)) ∧
      (∀ p : P, f (i p) = g (j p)) ∧
      (∀ x : C, ∀ y : B, f x = g y →
        ∃ p : P, x = i p ∧ y = j p) ∧
      K.IsTwoSparse (Finset.univ :
        Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset C).image f) Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset B).image g) Finset.univ ∧
      (∀ k : ℕ, k < m →
        FiniteC0.oldStage κFinal k =
          FiniteC0.oldStage κFinal (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κFinal k)
          (FiniteC0.oldStage κFinal (k+1))) ∧
      (∀ u : C,
        FiniteC0.canonicalValue K κFinal (f u) =
          (FiniteC0.canonicalValue G κ u).image f) := by
  classical
  obtain ⟨K, f, g, hf, hg, hAdjF, hAdjG, hBase, hOnly,
      hSparse, hStrongF, hStrongG'⟩ :=
    exists_finite_strong_free_amalgam
      G H i j hi hj hAgree hSparseG hSparseH hStrongG hStrongH
  obtain ⟨m, κFinal, hSteps, hValues⟩ :=
    FiniteC0.exists_canonical_extension_over_embedding
      G K f hf (fun x y => (hAdjF x y).symm) κ hOld hStrongF
  exact ⟨K, f, g, m, κFinal,
    hf, hg,
    (fun x y => (hAdjF x y).symm),
    (fun x y => (hAdjG x y).symm),
    hBase, hOnly, hSparse, hStrongF, hStrongG',
    hSteps, hValues⟩

end FiniteSpan
end BigHrushovski
