import BigHrushovski.FiniteNatStage
import BigHrushovski.GenericityCriterion

/-!
# Restrict an applicable Nat-labelled request to the finite stage carrier

An extension request in the fair catalogue has a map from its finite
source into the ambient natural numbers. If it applies to a stage whose
domain is the initial segment `range n`, this map factors through
`Fin n`. The induced source diagram, two-sparsity, and relative
strongness are exactly preserved under that finite-carrier transport.

This is the missing input conversion for applying finite strong
free amalgamation to a fair-scheduled request. The construction
of the next stage remains a separate obligation.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- An applicable source map into a Nat initial segment gives an
injective induced strong embedding into the corresponding `Fin n`
graph. No strongness outside the finite initial segment is assumed. -/
theorem exists_finite_applicable_source
    (G : GraphOn ℕ) (n : ℕ)
    (hSparse : G.IsTwoSparse (Finset.range n))
    (req : ExtensionRequestCatalogue)
    (hApp : AppliesAt G (Finset.range n) req) :
    ∃ f : Fin req.1 → Fin n,
      Function.Injective f ∧
      (∀ x : Fin req.1, (f x).val = req.2.2.2 x) ∧
      (∀ x y : Fin req.1,
        req.2.2.1.source.adj x y ↔
          (G.pullback (fun z : Fin n => z.val)).adj (f x) (f y)) ∧
      (G.pullback (fun z : Fin n => z.val)).IsTwoSparse
        (Finset.univ : Finset (Fin n)) ∧
      (G.pullback (fun z : Fin n => z.val)).toPredimension.IsStrong
        ((Finset.univ : Finset (Fin req.1)).image f)
        (Finset.univ : Finset (Fin n)) := by
  classical
  obtain ⟨hInj, hInduced, hStrong⟩ := hApp
  have hRange (x : Fin req.1) : req.2.2.2 x < n := by
    apply Finset.mem_range.mp
    exact hStrong.1 (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, rfl⟩)
  let f : Fin req.1 → Fin n :=
    fun x => ⟨req.2.2.2 x, hRange x⟩
  have hf : Function.Injective f := by
    intro x y h
    exact hInj (congrArg Fin.val h)
  have hImage :
      (((Finset.univ : Finset (Fin req.1)).image f).image
        (fun z : Fin n => z.val)) =
      (Finset.univ : Finset (Fin req.1)).image req.2.2.2 := by
    rw [Finset.image_image]
    congr 1
    funext x
    rfl
  have hSparseFin :
      (G.pullback (fun z : Fin n => z.val)).IsTwoSparse
        (Finset.univ : Finset (Fin n)) :=
    (G.twoSparse_pullback_fin_iff n).mpr hSparse
  have hStrongFin :
      (G.pullback (fun z : Fin n => z.val)).toPredimension.IsStrong
        ((Finset.univ : Finset (Fin req.1)).image f)
        (Finset.univ : Finset (Fin n)) := by
    apply (G.strong_pullback_fin_iff n
      ((Finset.univ : Finset (Fin req.1)).image f)).mpr
    rw [hImage]
    exact hStrong
  refine ⟨f, hf, (fun _ => rfl), ?_, hSparseFin, hStrongFin⟩
  intro x y
  exact hInduced x y

end FiniteCatalogue
end BigHrushovski
