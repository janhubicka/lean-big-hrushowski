import BigHrushovski.CFGlobalSourceStage
import BigHrushovski.CFCountableInduced

/-!
# Lift a prescribed finite d-closed embedding back to an actual C_F stage

The source preparation theorem already shows that any finite
globally d-closed image of the birth graph equals the image
of a d-closed finite-stage subset. For the extension property,
the embedding *map*, not just its image, must be retained.

Here the old source is a finite type S and a prescribed
injective induced map e:S→M into the countable birth graph
has globally strictly d-closed image. We choose one finite
stage containing that image and lift each e(s) to its
unique representative at the stage. The resulting embedding
is induced, its image is d-closed in the stage, and
composition with the canonical birth map is literally e.

No new edges or new vertices are constructed by this lemma.
Its role is to prepare the actual named old support Q=e[P]
for a later minimal-extension response without changing
the prescribed old embedding.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Every prescribed finite globally d-closed induced
embedding into the countable birth graph is literally the
birth image of a d-closed induced embedding into some
finite stage. The input map is preserved pointwise. -/
theorem prescribedClosedSource_liftToStage
    {S : Type*} [Fintype S] [DecidableEq S]
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (A : GraphOn S)
    (e : S → Vertex F K)
    (he : Function.Injective e)
    (hAdj : ∀ x y : S,
      A.adj x y ↔ (countableGraph F K).adj (e x) (e y))
    (hClosed :
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset S).image e)) :
    ∃ n : ℕ, ∃ f : S → (stage F K n).carrier,
      Function.Injective f ∧
      (∀ x y : S,
        A.adj x y ↔ (stage F K n).graph.adj (f x) (f y)) ∧
      (∀ x : S, toVertex F K n (f x) = e x) ∧
      (stage F K n).graph.toPredimension.IsDClosed
        ((Finset.univ : Finset S).image f) Finset.univ := by
  classical
  obtain ⟨n, a, haBirth, haClosed⟩ :=
    globalFiniteSource_in_dClosedStage F K
      ((Finset.univ : Finset S).image e) hClosed
  have hRep : ∀ x : S,
      ∃ v : (stage F K n).carrier,
        toVertex F K n v = e x := by
    intro x
    have hx :
        e x ∈ ((Finset.univ : Finset S).image e) :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    rw [haBirth] at hx
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hx
    exact ⟨v, heq⟩
  let f : S → (stage F K n).carrier :=
    fun x => Classical.choose (hRep x)
  have hfBirth : ∀ x : S, toVertex F K n (f x) = e x :=
    fun x => Classical.choose_spec (hRep x)
  have hfInjective : Function.Injective f := by
    intro x y hxy
    apply he
    calc
      e x = toVertex F K n (f x) := (hfBirth x).symm
      _ = toVertex F K n (f y) := by rw [hxy]
      _ = e y := hfBirth y
  have hfInduced : ∀ x y : S,
      A.adj x y ↔ (stage F K n).graph.adj (f x) (f y) := by
    intro x y
    calc
      A.adj x y ↔ (countableGraph F K).adj (e x) (e y) :=
        hAdj x y
      _ ↔ (stage F K n).graph.adj (f x) (f y) := by
        rw [← hfBirth x, ← hfBirth y]
        exact countableGraph_stage_induced F K n (f x) (f y)
  have hBirthImages :
      (((Finset.univ : Finset S).image f).image
        (toVertex F K n)) =
        a.image (toVertex F K n) := by
    calc
      (((Finset.univ : Finset S).image f).image
          (toVertex F K n)) =
        (Finset.univ : Finset S).image
          (fun x => toVertex F K n (f x)) := by
            rw [Finset.image_image]
      _ = (Finset.univ : Finset S).image e := by
            apply Finset.image_congr
            intro x _
            exact hfBirth x
      _ = a.image (toVertex F K n) := haBirth.symm
  have hImage : ((Finset.univ : Finset S).image f) = a :=
    (Finset.image_injective (toVertex_injective F K n))
      hBirthImages
  refine ⟨n, f, hfInjective, hfInduced, hfBirth, ?_⟩
  rw [hImage]
  exact haClosed

end CFCoherentTower
end BigHrushovski
