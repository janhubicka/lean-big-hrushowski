import BigHrushovski.C0FiniteFunctionalLift

/-!
# Canonical C0 functional presentations under arbitrary induced embeddings

An induced injection f:C→K identifies its domain with the literal
induced subgraph on the finite image f[C]. A canonical component
index κ:C→Fin n transports to this image by the inverse
equivalence. We prove both the minimal strong stage conditions and
the complete set-valued unary function are invariant under this
relabeling.

Applying the certified finite graph-to-functional lift to the
image f[C] then yields a canonical presentation on the whole K,
whose restriction to f[C] is exactly the prescribed old structure.

This is the remaining finite embedded-base interface in the
reduct-identification argument. No countable extension property is
asserted here.
-/

namespace BigHrushovski
namespace FiniteC0

variable {U W : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype W] [DecidableEq W]
variable {n : ℕ}

/-- Transport an entire finite component indexing through a bijection. -/
def relabelIndex (κ : U → Fin n) (e : U ≃ W) : W → Fin n :=
  fun w => κ (e.symm w)

/-- Direct backwards dependencies are unchanged by an induced
equivalence of their underlying finite graph vertices. -/
theorem backDependency_relabel_iff
    (G : GraphOn U) (H : GraphOn W) (e : U ≃ W)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (e x) (e y))
    (κ : U → Fin n) (i j : Fin n) :
    backDependency H (relabelIndex κ e) i j ↔
      backDependency G κ i j := by
  constructor
  · rintro ⟨hLt, u, v, hu, hv, hEdge⟩
    refine ⟨hLt, e.symm u, e.symm v, hu, hv, ?_⟩
    apply (hAdj (e.symm u) (e.symm v)).mpr
    simpa using hEdge
  · rintro ⟨hLt, u, v, hu, hv, hEdge⟩
    refine ⟨hLt, e u, e v, ?_, ?_, (hAdj u v).mp hEdge⟩
    · simpa [relabelIndex] using hu
    · simpa [relabelIndex] using hv

/-- Every full unary value transports exactly, including all vertices
of all reached components and arbitrarily long backwards paths. -/
theorem canonicalValue_relabel
    (G : GraphOn U) (H : GraphOn W) (e : U ≃ W)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (e x) (e y))
    (κ : U → Fin n) (u : U) :
    canonicalValue H (relabelIndex κ e) (e u) =
      (canonicalValue G κ u).image e := by
  classical
  have hRel :
      backDependency H (relabelIndex κ e) =
      backDependency G κ := by
    funext i j
    exact propext (backDependency_relabel_iff G H e hAdj κ i j)
  ext w
  constructor
  · intro hw
    have hp :
        TaggedAmalgam.DependencyAncestor
          (backDependency G κ) (κ u) (κ (e.symm w)) := by
      have h := (mem_canonicalValue_iff H
        (relabelIndex κ e) (e u) w).mp hw
      rw [hRel] at h
      simpa [relabelIndex] using h
    exact Finset.mem_image.mpr
      ⟨e.symm w,
        (mem_canonicalValue_iff G κ u (e.symm w)).mpr hp,
        e.apply_symm_apply w⟩
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    have hp :
        TaggedAmalgam.DependencyAncestor
          (backDependency G κ) (κ u) (κ v) :=
      (mem_canonicalValue_iff G κ u v).mp hv
    have hpNew :
        TaggedAmalgam.DependencyAncestor
          (backDependency H (relabelIndex κ e))
          (relabelIndex κ e (e u))
          (relabelIndex κ e (e v)) := by
      rw [hRel]
      simpa [relabelIndex] using hp
    rw [← hvw]
    exact (mem_canonicalValue_iff H
      (relabelIndex κ e) (e u) (e v)).mpr hpNew

/-- Each chronological stage is the literal image of the
corresponding original stage under the finite equivalence. -/
theorem oldStage_relabel
    (κ : U → Fin n) (e : U ≃ W) (k : ℕ) :
    oldStage (relabelIndex κ e) k =
      (oldStage κ k).image e := by
  classical
  ext w
  constructor
  · intro hw
    have hv : (κ (e.symm w)).val < k :=
      (mem_oldStage_iff (relabelIndex κ e) k w).mp hw
    exact Finset.mem_image.mpr
      ⟨e.symm w,
        (mem_oldStage_iff κ k (e.symm w)).mpr hv,
        e.apply_symm_apply w⟩
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    rw [← hvw]
    exact (mem_oldStage_iff (relabelIndex κ e) k (e v)).mpr
      (by simpa [relabelIndex] using
        (mem_oldStage_iff κ k v).mp hv)

/-- Reindexing across an induced equivalence preserves the exact
empty-or-minimal-strong status of every finite component step. -/
theorem minimalSteps_relabel
    (G : GraphOn U) (H : GraphOn W) (e : U ≃ W)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (e x) (e y))
    (κ : U → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) :
    ∀ k : ℕ, k < n →
      oldStage (relabelIndex κ e) k =
        oldStage (relabelIndex κ e) (k+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage (relabelIndex κ e) k)
        (oldStage (relabelIndex κ e) (k+1)) := by
  classical
  intro k hk
  rcases hOld k hk with hEq | hMin
  · left
    rw [oldStage_relabel κ e k, oldStage_relabel κ e (k+1), hEq]
  · right
    have hMono : oldStage κ k ⊆ oldStage κ (k+1) := by
      intro u hu
      have huLt : (κ u).val < k := (mem_oldStage_iff κ k u).mp hu
      exact (mem_oldStage_iff κ (k+1) u).mpr (by omega)
    have hImage :
        H.toPredimension.IsMinimalStrongStep
          ((oldStage κ k).image e) ((oldStage κ (k+1)).image e) :=
      (G.minimalStrongStep_image_iff H e e.injective hAdj
        (oldStage κ k) (oldStage κ (k+1)) hMono).mpr hMin
    rw [← oldStage_relabel κ e k,
      ← oldStage_relabel κ e (k+1)] at hImage
    exact hImage

/-- The subtype of the image of an injected finite graph is
equivalent to the whole source domain. -/
noncomputable def imageCarrierEquiv
    (f : U → W) (hf : Function.Injective f) :
    U ≃ {w : W // w ∈ (Finset.univ : Finset U).image f} where
  toFun u := ⟨f u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩
  invFun w := Classical.choose (Finset.mem_image.mp w.property)
  left_inv := by
    intro u
    apply hf
    exact (Classical.choose_spec
      (Finset.mem_image.mp
        (show f u ∈ (Finset.univ : Finset U).image f from
          Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩))).2
  right_inv := by
    intro w
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp w.property)).2

/-- A canonical finite functional presentation of the source graph
transports to the actual induced image of any injected induced
embedding, with both stages and complete unary values preserved. -/
theorem canonicalPresentation_on_image
    (G : GraphOn U) (K : GraphOn W)
    (f : U → W) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ K.adj (f x) (f y))
    (κ : U → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) :
    let a : Finset W := (Finset.univ : Finset U).image f
    let H := K.pullback (Subtype.val : {w : W // w ∈ a} → W)
    let e := imageCarrierEquiv f hf
    let κa := relabelIndex κ e
    (∀ k : ℕ, k < n →
      oldStage κa k = oldStage κa (k+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage κa k) (oldStage κa (k+1))) ∧
    (∀ u : U,
      (canonicalValue H κa (e u)).image
        (Subtype.val : {w : W // w ∈ a} → W) =
      (canonicalValue G κ u).image f) := by
  classical
  let a : Finset W := (Finset.univ : Finset U).image f
  let H := K.pullback (Subtype.val : {w : W // w ∈ a} → W)
  let e := imageCarrierEquiv f hf
  let κa := relabelIndex κ e
  have hAdjImage : ∀ x y : U,
      G.adj x y ↔ H.adj (e x) (e y) := by
    intro x y
    exact hAdj x y
  constructor
  · exact minimalSteps_relabel G H e hAdjImage κ hOld
  · intro u
    have hVals := canonicalValue_relabel G H e hAdjImage κ u
    rw [hVals, Finset.image_image]
    have hComp :
        (Subtype.val : {w : W // w ∈ a} → W) ∘ e = f := by
      funext x
      rfl
    rw [hComp]

/-- Any finite strong graph extension of the image of an induced
embedding admits a canonical functional presentation preserving the
original complete unary values along the supplied embedding.

This theorem includes the arbitrary change of old coordinates
required to apply the previously certified literal-inclusion
lifting theorem to a tagged strong free amalgam. -/
theorem exists_canonical_extension_over_embedding
    (G : GraphOn U) (K : GraphOn W)
    (f : U → W) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ K.adj (f x) (f y))
    (κ : U → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (hStrong : K.toPredimension.IsStrong
      ((Finset.univ : Finset U).image f) Finset.univ) :
    ∃ (m : ℕ) (κFinal : W → Fin m),
      (∀ k : ℕ, k < m →
        oldStage κFinal k = oldStage κFinal (k+1) ∨
        K.toPredimension.IsMinimalStrongStep
          (oldStage κFinal k) (oldStage κFinal (k+1))) ∧
      (∀ u : U,
        canonicalValue K κFinal (f u) =
          (canonicalValue G κ u).image f) := by
  classical
  let a : Finset W := (Finset.univ : Finset U).image f
  let H := K.pullback (Subtype.val : {w : W // w ∈ a} → W)
  let e := imageCarrierEquiv f hf
  let κa := relabelIndex κ e
  obtain ⟨hStagesImage, hValuesImage⟩ :=
    canonicalPresentation_on_image G K f hf hAdj κ hOld
  obtain ⟨m, κFinal, hFinal, hOldValues⟩ :=
    exists_canonical_extension_of_strong
      K a κa hStagesImage hStrong
  refine ⟨m, κFinal, hFinal, ?_⟩
  intro u
  have hValue := hOldValues (e u)
  have hOldEq := hValuesImage u
  change canonicalValue K κFinal (f u) =
    (canonicalValue H κa (e u)).image
      (Subtype.val : {w : W // w ∈ a} → W) at hValue
  exact hValue.trans hOldEq

end FiniteC0
end BigHrushovski
