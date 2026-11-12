import BigHrushovski.CFStageBirthOrderCoherence
import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity

/-!
# Recover ordered finite-stage supports from a partial birth map

The source and target of a finite C_F lift need not have an
embedding between their whole old stages. What is available is
an embedding on the finite closed source and an exact image
of each particular named old support.

We recover an order isomorphism of the *literal old-stage
support coordinates* from this data. The proof uses the exact
birth-vertex inclusions at the two stages, preservation of the
canonical birth order, and equality of the finite support
images. Neither the source nor the target old stage is required
to contain any vertex outside the named support.

This is the stage-coordinate bridge needed to turn the abstract
complete-support equality and block rigidity into the ordered
coordinate maps of the one-level request-code uniqueness theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Regard a finite-stage old support vertex as a vertex of an
actual finite source s. The inclusion is literally the canonical
birth map and is defined as soon as the whole named support
is contained in s. -/
noncomputable def finiteStageSupportPoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n : ℕ) (P : Finset (stage F K n).carrier)
    (hP : P.image (toVertex F K n) ⊆ s) :
    SupportCarrier (stage F K n).carrier P →
      SupportCarrier (Vertex F K) s :=
  fun u => ⟨toVertex F K n u.val,
    hP (Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩)⟩

/-- Each literal stage support point lies in the original
selected subset of s corresponding to the complete named
stage support. There is no arbitrary source-stage numbering. -/
theorem finiteStageSupportPoint_selected
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n : ℕ) (P : Finset (stage F K n).carrier)
    (hP : P.image (toVertex F K n) ⊆ s)
    (u : SupportCarrier (stage F K n).carrier P) :
    finiteStageSupportPoint F K s n P hP u ∈
      selectedFiniteSet s (P.image (toVertex F K n)) := by
  classical
  simpa [selectedFiniteSet, finiteStageSupportPoint] using
    (Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩ :
      (toVertex F K n u.val) ∈ P.image (toVertex F K n))

/-- An embedding defined only on the finite source s gives a
unique ordered coordinate bijection between two *particular*
named old supports P and Q, provided it maps the complete
selected image of P exactly onto the birth image of Q.

This is a bijection of the genuine finite-stage support
subtypes, not a map of whole source/target stages. It works
even when the target stage is U_0 and both supports are empty.
No free-amalgamation or C_F growth hypothesis is needed. -/
noncomputable def finiteStageSupportOrderIso
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ)
    (P : Finset (stage F K n).carrier)
    (Q : Finset (stage F K m).carrier)
    (hP : P.image (toVertex F K n) ⊆ s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (hImage :
      (selectedFiniteSet s
        (P.image (toVertex F K n))).image e =
          Q.image (toVertex F K m))
    (hOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y)) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier :=
      stageLinearOrder F K m
    SupportCarrier (stage F K n).carrier P ≃o
      SupportCarrier (stage F K m).carrier Q := by
  classical
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  let src : SupportCarrier (stage F K n).carrier P →
      SupportCarrier (Vertex F K) s :=
    finiteStageSupportPoint F K s n P hP
  have hSrcSelected : ∀ u : SupportCarrier (stage F K n).carrier P,
      src u ∈ selectedFiniteSet s
        (P.image (toVertex F K n)) := by
    intro u
    exact finiteStageSupportPoint_selected F K s n P hP u
  have hTarget : ∀ u : SupportCarrier (stage F K n).carrier P,
      e (src u) ∈ Q.image (toVertex F K m) := by
    intro u
    rw [← hImage]
    exact Finset.mem_image.mpr
      ⟨src u, hSrcSelected u, rfl⟩
  have hExists : ∀ u : SupportCarrier (stage F K n).carrier P,
      ∃ v : SupportCarrier (stage F K m).carrier Q,
        toVertex F K m v.val = e (src u) := by
    intro u
    obtain ⟨v, hv, hvEq⟩ := Finset.mem_image.mp (hTarget u)
    exact ⟨⟨v, hv⟩, hvEq⟩
  let g : SupportCarrier (stage F K n).carrier P →
      SupportCarrier (stage F K m).carrier Q :=
    fun u => Classical.choose (hExists u)
  have hg : ∀ u : SupportCarrier (stage F K n).carrier P,
      toVertex F K m (g u).val = e (src u) := by
    intro u
    exact Classical.choose_spec (hExists u)
  have hgMono : StrictMono g := by
    intro u v huv
    have hSource : stageLt F K n u.val v.val := huv
    have hBorn :
        canonicalBirthLt F K (src u).val (src v).val :=
      (stageLt_iff_canonicalBirthLt F K n u.val v.val).mp hSource
    have hTargetLt :
        canonicalBirthLt F K (e (src u)) (e (src v)) :=
      (hOrder (src u) (src v)).mp hBorn
    have hStage :
        stageLt F K m (g u).val (g v).val := by
      apply (stageLt_iff_canonicalBirthLt F K m
        (g u).val (g v).val).mpr
      rw [hg u, hg v]
      exact hTargetLt
    exact hStage
  have hgSurj : Function.Surjective g := by
    intro v
    have hvQ :
        toVertex F K m v.val ∈ Q.image (toVertex F K m) :=
      Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
    have hvImage :
        toVertex F K m v.val ∈
          (selectedFiniteSet s
            (P.image (toVertex F K n))).image e := by
      rw [hImage]
      exact hvQ
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hvImage
    have hxP : x.val ∈ P.image (toVertex F K n) := by
      simpa [selectedFiniteSet] using hx
    obtain ⟨u, hu, huEq⟩ := Finset.mem_image.mp hxP
    let p : SupportCarrier (stage F K n).carrier P := ⟨u, hu⟩
    have hSrc : src p = x := by
      apply Subtype.ext
      exact huEq
    have hEq : toVertex F K m (g p).val =
        toVertex F K m v.val := by
      calc
        toVertex F K m (g p).val = e (src p) := hg p
        _ = e x := congrArg e hSrc
        _ = toVertex F K m v.val := hxeq
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact (toVertex_injective F K m) hEq
  exact OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono g hgMono) hgSurj

end CFCoherentTower
end BigHrushovski
