import BigHrushovski.HrushovskiEllentuckCFBirthSupport
import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity

/-!
# Complete support transport on a genuinely finite closed source

The global support-transport lemma previously demanded preservation
of complete b-values at every vertex of the countable carrier.
A prescribed finite C_F lift is only defined on a finite b-closed
source; extending it outside that source is *not* a graph embedding.

Here we localize the argument to the complete generated closure
of a vertex in the finite source. The complete b-value equation on
that closure already yields exact transport of its generated
closure and all represented birth levels.

The second theorem applies this to the existing finite prescribed
lift, with the exact prescribed target birth levels. This is an
independent finite step toward the full copy-range recognition
theorem, not a countable self-embedding or a uniqueness theorem.
-/

namespace BigHrushovski.Ellentuck

universe u v

variable {Vertex : Type u} {Level : Type v}
variable [DecidableEq Vertex] [DecidableEq Level]

/-- Exact image of a *single* generated finite support needs closure
transport only at x and level transport only on the finite closure
of x. There is no global preservation assumption. -/
theorem generatedSupport_image_on
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (f : Vertex → Vertex) (h : Level → Level) (x : Vertex)
    (hΓ : (Γ x).image f = Γ (f x))
    (hπ : ∀ w ∈ Γ x, π (f w) = h (π w)) :
    (generatedSupport Γ π x).image h =
      generatedSupport Γ π (f x) := by
  classical
  simp only [generatedSupport]
  rw [← hΓ]
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro w hw
  exact (hπ w hw).symm

end BigHrushovski.Ellentuck

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- Any partial map of a finite b-closed source preserving its
*complete* restricted b-values and prescribed birth levels
transports the full generated birth-level support of every
source vertex. No map outside the finite source has any
embedding property. Injectivity is not needed for this lemma. -/
theorem finiteClosedEmbedding_birthLevelSupport_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (level : ℕ → ℕ)
    (heLevel : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1)
    (x : SupportCarrier (Vertex F K) s) :
    (birthLevelSupport F K x.val).image level =
      birthLevelSupport F K (e x) := by
  classical
  let X : Set (Vertex F K) := {v | v ∈ s}
  let f := extendClosedSourceMap F K X e
  have hOn : ∀ v : Vertex F K, (hv : v ∈ s) →
      f v = e ⟨v, hv⟩ := by
    intro v hv
    exact extendClosedSourceMap_apply F K X e v hv
  have hBfull : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) :=
    arbitraryFiniteEmbedding_extendedBValues F K s hs e heB
  have hSub :
      birthSingletonClosure F K x.val ⊆ s := by
    change birthGeneratedClosure F K
      ({x.val} : Finset (Vertex F K)) ⊆ s
    exact birthGeneratedClosure_le_of_closed F K
      ({x.val} : Finset (Vertex F K)) s
      (by simpa using x.property) hs
  have hC :
      (birthSingletonClosure F K x.val).image f =
        birthSingletonClosure F K (f x.val) := by
    have hImage :=
      birthGeneratedClosure_image_of_bValues F K f
        ({x.val} : Finset (Vertex F K))
        (fun v hv => hBfull v (hSub hv))
    simpa only [birthSingletonClosure, Finset.image_singleton] using hImage
  have hπ :
      ∀ v ∈ birthSingletonClosure F K x.val,
        (f v).1 = level v.1 := by
    intro v hv
    have hvS : v ∈ s := hSub hv
    calc
      (f v).1 = (e ⟨v, hvS⟩).1 := congrArg (fun w : Vertex F K => w.1)
        (hOn v hvS)
      _ = level v.1 := heLevel ⟨v, hvS⟩
  have hImage :=
    Ellentuck.generatedSupport_image_on
      (birthSingletonClosure F K)
      (fun v : Vertex F K => v.1) f level x.val hC hπ
  have hfx : f x.val = e x := by
    simpa using hOn x.val x.property
  simpa only [birthLevelSupport, hfx] using hImage

/-- The same exact support equation for the *constructed*
prescribed finite lift. Only levels occurring in s need be
strictly increasing; the assignment on unused levels is arbitrary. -/
theorem finiteSourcePrescribedLift_birthLevelSupport_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x : SupportCarrier (Vertex F K) s) :
    (birthLevelSupport F K x.val).image level =
      birthLevelSupport F K
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover x) := by
  apply finiteClosedEmbedding_birthLevelSupport_image
    F K s hs
    (finiteSourcePrescribedLift F K s hs level hStrict n hCover)
    (fun w => ?_) level
    (fun w => finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrict n hCover w) x
  exact finiteSourceLiftOfCut_birthBValues F K s hs n
    (assignedTargetStage F K s level n) hCover
    (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map w

/-- A finite prescribed lift preserves membership of a vertex in
every complete-support domain, after pulling the selected level
set back along the prescribed assignment. The target level set
need not be an initial segment or even be finite. -/
theorem finiteSourcePrescribedLift_birthLevelDomain_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (T : Set ℕ) (x : SupportCarrier (Vertex F K) s) :
    x.val ∈ birthLevelDomain F K (level ⁻¹' T) ↔
      finiteSourcePrescribedLift F K s hs level hStrict n hCover x ∈
        birthLevelDomain F K T := by
  have hSupport :=
    finiteSourcePrescribedLift_birthLevelSupport_image
      F K s hs level hStrict n hCover x
  change
    (∀ q ∈ birthLevelSupport F K x.val, level q ∈ T) ↔
      (∀ q ∈ birthLevelSupport F K
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover x),
          q ∈ T)
  rw [← hSupport]
  constructor
  · intro hx q hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    rw [← hpq]
    exact hx p hp
  · intro hx p hp
    exact hx (level p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

end BigHrushovski.CFCoherentTower
