import BigHrushovski.C0FiniteCanonicalHeredity
import BigHrushovski.C0MinimalImage
import BigHrushovski.SpanNormalization

/-!
# Restriction of canonical C0 unary values to a finite closed substructure

Let s be a finite subset closed under the canonical full component
closure of a finite C0 presentation κ:V→Fin n. The induced graph on
the subtype W={v∈V | v∈s} retains the original component indices.

Every backwards dependency path in the subtype is plainly a path
in the original graph. Conversely, a path starting at u∈s may be
lifted into the subtype: closure of s under the *complete* unary
value of u contains every vertex in each component visited by the
path, including the two endpoints witnessing each dependency edge.

Thus the canonically defined set-valued unary function of the
induced subtype agrees exactly with the restriction of the original
function, without reindexing the retained components.

In combination with C0FiniteCanonicalHeredity, this proves the
whole finite hereditary assertion of the intrinsic functional age:
empty index positions are allowed, and every nonempty retained
block stays minimal strong after restriction.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- The original finite component-indexing restricted to a subtype. -/
def restrictIndex (κ : V → Fin n) (s : Finset V) :
    {v : V // v ∈ s} → Fin n :=
  fun v => κ v.val

/-- Every dependency edge in the restricted induced graph is a
dependency of the same two component indices in the original graph. -/
theorem restrictDependency_to_original
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V) (i j : Fin n)
    (h : backDependency
      (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
      (restrictIndex κ s) i j) :
    backDependency G κ i j := by
  obtain ⟨hLt, u, v, hu, hv, hAdj⟩ := h
  exact ⟨hLt, u.val, v.val, hu, hv, hAdj⟩

/-- Starting in the closed subtype, complete component reachability
does not change when passing to the induced graph. -/
theorem restrictAncestor_iff
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (root : {v : V // v ∈ s}) (j : Fin n) :
    TaggedAmalgam.DependencyAncestor
      (backDependency
        (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
        (restrictIndex κ s))
      (restrictIndex κ s root) j ↔
    TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ root.val) j := by
  constructor
  · intro h
    induction h with
    | root => exact TaggedAmalgam.DependencyAncestor.root
    | @step i j hPrev hDep ih =>
        exact TaggedAmalgam.DependencyAncestor.step ih
          (restrictDependency_to_original G κ s i j hDep)
  · intro h
    induction h with
    | root => exact TaggedAmalgam.DependencyAncestor.root
    | @step i j hPrev hDep ih =>
        obtain ⟨hLt, u, v, hu, hv, hAdj⟩ := hDep
        have hA : TaggedAmalgam.DependencyAncestor
            (backDependency G κ) (κ root.val) (κ u) := by
          rw [hu]
          exact hPrev
        have hB : TaggedAmalgam.DependencyAncestor
            (backDependency G κ) (κ root.val) (κ v) := by
          rw [hv]
          exact TaggedAmalgam.DependencyAncestor.step hPrev
            ⟨hLt, u, v, hu, hv, hAdj⟩
        have huValue : u ∈ canonicalValue G κ root.val :=
          (mem_canonicalValue_iff G κ root.val u).mpr hA
        have hvValue : v ∈ canonicalValue G κ root.val :=
          (mem_canonicalValue_iff G κ root.val v).mpr hB
        have huS : u ∈ s := hClosed root.val root.property huValue
        have hvS : v ∈ s := hClosed root.val root.property hvValue
        let us : {v : V // v ∈ s} := ⟨u, huS⟩
        let vs : {v : V // v ∈ s} := ⟨v, hvS⟩
        have hDepS : backDependency
            (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
            (restrictIndex κ s) i j := by
          refine ⟨hLt, us, vs, ?_, ?_, ?_⟩
          · exact hu
          · exact hv
          · exact hAdj
        exact TaggedAmalgam.DependencyAncestor.step ih hDepS

/-- The inherited unary value on the induced closed subtype is the
complete original unary value, transported by the subtype inclusion.
This is the exact finite set-valued function identity needed for
heredity of the canonical C0 functional age. -/
theorem canonicalValue_restrict_image
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u : {v : V // v ∈ s}) :
    (canonicalValue
      (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
      (restrictIndex κ s) u).image
        (Subtype.val : {v : V // v ∈ s} → V) =
      canonicalValue G κ u.val := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    have hwAnc :
        TaggedAmalgam.DependencyAncestor
          (backDependency
            (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
            (restrictIndex κ s))
          (restrictIndex κ s u) (restrictIndex κ s w) :=
      (mem_canonicalValue_iff
        (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
        (restrictIndex κ s) u w).mp hw
    have hOriginal :
        TaggedAmalgam.DependencyAncestor
          (backDependency G κ) (κ u.val) (κ w.val) :=
      (restrictAncestor_iff G κ s hClosed u (κ w.val)).mp hwAnc
    rw [← hwv]
    exact (mem_canonicalValue_iff G κ u.val w.val).mpr hOriginal
  · intro hv
    have hvS : v ∈ s := hClosed u.val u.property hv
    let w : {v : V // v ∈ s} := ⟨v, hvS⟩
    have hOriginal :
        TaggedAmalgam.DependencyAncestor
          (backDependency G κ) (κ u.val) (κ v) :=
      (mem_canonicalValue_iff G κ u.val v).mp hv
    have hRestricted :=
      (restrictAncestor_iff G κ s hClosed u (κ v)).mpr hOriginal
    refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
    exact (mem_canonicalValue_iff
      (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
      (restrictIndex κ s) u w).mpr hRestricted

/-- The old prefix in the induced subtype has as its image
precisely the part of the original old prefix selected by s. -/
theorem oldStage_restrict_image
    (κ : V → Fin n) (s : Finset V) (k : ℕ) :
    (oldStage (restrictIndex κ s) k).image
      (Subtype.val : {v : V // v ∈ s} → V) =
        s ∩ oldStage κ k := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    have hLess : (κ w.val).val < k :=
      (mem_oldStage_iff (restrictIndex κ s) k w).mp hw
    rw [← hwv]
    exact Finset.mem_inter.mpr
      ⟨w.property, (mem_oldStage_iff κ k w.val).mpr hLess⟩
  · intro hv
    obtain ⟨hvS, hvOld⟩ := Finset.mem_inter.mp hv
    have hLess : (κ v).val < k :=
      (mem_oldStage_iff κ k v).mp hvOld
    exact Finset.mem_image.mpr
      ⟨⟨v, hvS⟩,
        (mem_oldStage_iff (restrictIndex κ s) k ⟨v, hvS⟩).mpr hLess,
        rfl⟩

/-- Every restricted stage is either unchanged or a minimal strong
extension in the *induced graph on the closed subset*. -/
theorem canonicalValue_restrict_minimalSteps
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (k : ℕ) (hk : k < n) :
    let H := G.pullback
      (Subtype.val : {v : V // v ∈ s} → V)
    let κs := restrictIndex κ s
    oldStage κs (k+1) = oldStage κs k ∨
    H.toPredimension.IsMinimalStrongStep
      (oldStage κs k) (oldStage κs (k+1)) := by
  classical
  let H := G.pullback
    (Subtype.val : {v : V // v ∈ s} → V)
  let κs := restrictIndex κ s
  have hCut := canonicalValue_closed_cut_step G κ hMin s hClosed k hk
  rcases hCut with hEqual | hStep
  · left
    apply Finset.image_injective
      (Subtype.val_injective : Function.Injective
        (Subtype.val : {v : V // v ∈ s} → V))
    rw [oldStage_restrict_image κ s (k+1),
        oldStage_restrict_image κ s k]
    exact hEqual
  · right
    have hSubset : oldStage κs k ⊆ oldStage κs (k+1) := by
      intro w hw
      have hLt : (κs w).val < k :=
        (mem_oldStage_iff κs k w).mp hw
      exact (mem_oldStage_iff κs (k+1) w).mpr (by omega)
    have hImage :
        G.toPredimension.IsMinimalStrongStep
          ((oldStage κs k).image (Subtype.val : {v : V // v ∈ s} → V))
          ((oldStage κs (k+1)).image (Subtype.val : {v : V // v ∈ s} → V)) := by
      rw [oldStage_restrict_image κ s k,
          oldStage_restrict_image κ s (k+1)]
      exact hStep
    have hAdj : ∀ x y : {v : V // v ∈ s},
        H.adj x y ↔ G.adj x.val y.val := fun _ _ => Iff.rfl
    exact (H.minimalStrongStep_image_iff G
      (Subtype.val : {v : V // v ∈ s} → V)
      Subtype.val_injective hAdj
      (oldStage κs k) (oldStage κs (k+1)) hSubset).mp hImage

end FiniteC0
end BigHrushovski
