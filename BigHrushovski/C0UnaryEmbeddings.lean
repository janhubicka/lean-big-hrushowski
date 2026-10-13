import BigHrushovski.C0UnaryClosedStrong

/-!
# Embeddings preserving the C0 unary closure function

An embedding of the concrete countable unary presentation is an
injective induced graph embedding f such that

    f[C(v)] = C(f(v))

for every vertex v. We prove consequences needed when comparing
this presentation with component/back-edge descriptions:

* membership in unary closures is preserved and reflected;
* whole closure-components are mapped onto whole components;
* the image of the whole structure is closed under unary values;
* finite generated closures are transported exactly;
* images of finite unary-closed sets are finite unary-closed,
  and hence globally strong in the underlying graph.

The converse characterization using the directed back-edge
description remains to be established separately. No Ramsey
or Fraisse extension result is inferred here.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- An induced self-embedding preserving the entire value of the
unary set-valued closure function on every input vertex. -/
def IsGenericC0UnaryEmbedding (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧
  (∀ u v : ℕ,
    genericTwoSparseGraph.adj u v ↔
      genericTwoSparseGraph.adj (f u) (f v)) ∧
  (∀ v : ℕ,
    (genericC0UnaryClosure v).image f =
      genericC0UnaryClosure (f v))

/-- Membership in named unary closure is both preserved and
reflected by a genuine functional embedding. -/
theorem genericC0UnaryEmbedding_mem_iff
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (v w : ℕ) :
    w ∈ genericC0UnaryClosure v ↔
      f w ∈ genericC0UnaryClosure (f v) := by
  have hVal := hf.2.2 v
  constructor
  · intro hw
    rw [← hVal]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  · intro hw
    rw [← hVal] at hw
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hw
    have huw : u = w := hf.1 hfu
    simpa only [huw] using hu

/-- The image of a whole closure-component is exactly the whole
component containing the image of any of its vertices. -/
theorem genericC0UnaryEmbedding_component_image
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (v : ℕ) :
    (genericC0Component (genericC0ComponentIndex v)).image f =
      genericC0Component (genericC0ComponentIndex (f v)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hwv, hvw⟩ :=
      (genericC0Component_mem_iff_mutual v w).mp hw
    apply (genericC0Component_mem_iff_mutual (f v) (f w)).mpr
    exact ⟨(genericC0UnaryEmbedding_mem_iff hf v w).mp hwv,
      (genericC0UnaryEmbedding_mem_iff hf w v).mp hvw⟩
  · intro hy
    obtain ⟨hyv, hvy⟩ :=
      (genericC0Component_mem_iff_mutual (f v) y).mp hy
    have hVal := hf.2.2 v
    have hImage : y ∈ (genericC0UnaryClosure v).image f := by
      rw [hVal]
      exact hyv
    obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hImage
    have hBack : f v ∈ genericC0UnaryClosure (f w) := by
      rw [hfw]
      exact hvy
    have hRecip : v ∈ genericC0UnaryClosure w :=
      (genericC0UnaryEmbedding_mem_iff hf w v).mpr hBack
    have hwComp :
        w ∈ genericC0Component (genericC0ComponentIndex v) :=
      (genericC0Component_mem_iff_mutual v w).mpr ⟨hw, hRecip⟩
    exact Finset.mem_image.mpr ⟨w, hwComp, hfw⟩

/-- A functional embedding cannot create a second component
index for a previously selected component. -/
theorem genericC0UnaryEmbedding_component_eq_iff
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (u v : ℕ) :
    genericC0ComponentIndex u = genericC0ComponentIndex v ↔
      genericC0ComponentIndex (f u) = genericC0ComponentIndex (f v) := by
  constructor
  · intro h
    obtain ⟨hvu, huv⟩ :=
      (genericC0SameComponent_iff_mutual u v).mp h
    exact (genericC0SameComponent_iff_mutual (f u) (f v)).mpr
      ⟨(genericC0UnaryEmbedding_mem_iff hf u v).mp hvu,
       (genericC0UnaryEmbedding_mem_iff hf v u).mp huv⟩
  · intro h
    obtain ⟨hvu, huv⟩ :=
      (genericC0SameComponent_iff_mutual (f u) (f v)).mp h
    exact (genericC0SameComponent_iff_mutual u v).mpr
      ⟨(genericC0UnaryEmbedding_mem_iff hf u v).mpr hvu,
       (genericC0UnaryEmbedding_mem_iff hf v u).mpr huv⟩

/-- Every vertex of the target closure of a point of the image
is again in the image: this is set-valued substructure closure. -/
theorem genericC0UnaryEmbedding_range_closed
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (v w : ℕ) (hw : w ∈ genericC0UnaryClosure (f v)) :
    ∃ u : ℕ, f u = w := by
  have hVal := hf.2.2 v
  rw [← hVal] at hw
  obtain ⟨u, _, hfu⟩ := Finset.mem_image.mp hw
  exact ⟨u, hfu⟩

/-- The closure of a finite set is transported exactly, not
merely included in the closure of its image. -/
theorem genericC0UnaryEmbedding_generated_image
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (s : Finset ℕ) :
    (genericC0GeneratedClosure s).image f =
      genericC0GeneratedClosure (s.image f) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hy
    obtain ⟨v, hvs, hwv⟩ :=
      (mem_genericC0GeneratedClosure_iff s w).mp hw
    have hCl : f w ∈ genericC0UnaryClosure (f v) :=
      (genericC0UnaryEmbedding_mem_iff hf v w).mp hwv
    rw [hfw] at hCl
    exact (mem_genericC0GeneratedClosure_iff (s.image f) y).mpr
      ⟨f v, Finset.mem_image.mpr ⟨v, hvs, rfl⟩, hCl⟩
  · intro hy
    obtain ⟨z, hz, hyz⟩ :=
      (mem_genericC0GeneratedClosure_iff (s.image f) y).mp hy
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hz
    have hY : y ∈ genericC0UnaryClosure (f v) := by
      rw [hfv]
      exact hyz
    have hVal := hf.2.2 v
    rw [← hVal] at hY
    obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hY
    exact Finset.mem_image.mpr
      ⟨w, (mem_genericC0GeneratedClosure_iff s w).mpr
        ⟨v, hv, hw⟩, hfw⟩

/-- The image of every finite unary-closed domain is again
unary-closed, as required for a functional embedding. -/
theorem genericC0UnaryEmbedding_closed_image
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) :
    IsGenericC0UnaryClosed (s.image f) := by
  apply (genericC0UnaryClosed_iff_generated_eq_self (s.image f)).mpr
  calc
    genericC0GeneratedClosure (s.image f) =
      (genericC0GeneratedClosure s).image f :=
        (genericC0UnaryEmbedding_generated_image hf s).symm
    _ = s.image f := by
      rw [(genericC0UnaryClosed_iff_generated_eq_self s).mp hs]

/-- Every finite closed image is a globally strong induced
subgraph of M0; this uses the separately verified strongness
theorem for finite unary-closed sets. -/
theorem genericC0UnaryEmbedding_closed_image_global
    {f : ℕ → ℕ} (hf : IsGenericC0UnaryEmbedding f)
    (s : Finset ℕ) (hs : IsGenericC0UnaryClosed s) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (s.image f) :=
  genericC0UnaryClosed_global (s.image f)
    (genericC0UnaryEmbedding_closed_image hf s hs)

end FiniteCatalogue
end BigHrushovski
