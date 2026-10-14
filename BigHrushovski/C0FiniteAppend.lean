import BigHrushovski.C0FinitePrefixPersistence
import BigHrushovski.C0MinimalImage

/-!
# Appending a final component to a finite canonical C0 presentation

Suppose a finite induced subgraph on old vertices a is equipped with
a canonical component indexing κ : a → Fin n. Give every old vertex
its old index cast into Fin (n+1), and place every fresh vertex of the
larger finite graph into the final component at index n.

The first n stages are exactly the original finite stages embedded in
the enlarged graph, while stage n is precisely the old vertex set a.
All previous minimal strong steps are preserved by inducedness.
If a < V is a minimal strong extension, the new last step is too.

The crucial functional claim is stronger: the full set-valued unary
function of every old vertex is *identical* to its previous value,
transported along the old inclusion. This holds even if the newly
appended component has edges to old vertices, because all dependency
arrows point from later components to earlier ones.

No global strongness or countable construction is assumed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- Retain each old component index and give all fresh vertices
the last index. -/
noncomputable def appendIndex (a : Finset V)
    (κ : {v : V // v ∈ a} → Fin n) (v : V) : Fin (n+1) :=
  if h : v ∈ a then (κ ⟨v,h⟩).castSucc else Fin.last n

@[simp] theorem appendIndex_old
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (v : {v : V // v ∈ a}) :
    appendIndex a κ v.val = (κ v).castSucc := by
  simp only [appendIndex, dif_pos v.property]

theorem appendIndex_fresh
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (v : V) (hv : v ∉ a) :
    appendIndex a κ v = Fin.last n := by
  simp [appendIndex, hv]

/-- Every stage before the final fresh block is exactly the image
of the corresponding old stage. -/
theorem oldStage_append_image
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (k : ℕ) (hk : k ≤ n) :
    oldStage (appendIndex a κ) k =
      (oldStage κ k).image (Subtype.val : {v : V // v ∈ a} → V) := by
  classical
  ext v
  constructor
  · intro hv
    have hlt : (appendIndex a κ v).val < k :=
      (mem_oldStage_iff (appendIndex a κ) k v).mp hv
    by_cases ha : v ∈ a
    · exact Finset.mem_image.mpr
        ⟨⟨v,ha⟩,
          (mem_oldStage_iff κ k ⟨v,ha⟩).mpr (by
            have hIdx := appendIndex_old a κ ⟨v,ha⟩
            rw [hIdx] at hlt
            exact hlt), rfl⟩
    · have hlast : appendIndex a κ v = Fin.last n :=
        appendIndex_fresh a κ v ha
      rw [hlast] at hlt
      simp only [Fin.val_last] at hlt
      omega
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    have hlt : (κ u).val < k :=
      (mem_oldStage_iff κ k u).mp hu
    have hOld : (appendIndex a κ u.val).val < k := by
      rw [appendIndex_old a κ u]
      exact hlt
    rw [← huv]
    exact (mem_oldStage_iff (appendIndex a κ) k u.val).mpr hOld

/-- Stage n contains exactly the old graph, not merely an isomorphic
copy or a chosen superset of it. -/
theorem oldStage_append_old
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n) :
    oldStage (appendIndex a κ) n = a := by
  classical
  rw [oldStage_append_image a κ n (le_refl n), oldStage_final κ]
  ext v
  constructor
  · intro hv
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hv
    rw [← hw]
    exact w.property
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

/-- Back edges between old components agree after casting their
indices into Fin (n+1). -/
theorem backDependency_castSucc_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphOn W) (κ : W → Fin n)
    (i j : Fin n) :
    backDependency H (fun v => (κ v).castSucc) i.castSucc j.castSucc ↔
      backDependency H κ i j := by
  constructor
  · rintro ⟨hLt,u,v,hu,hv,hAdj⟩
    have hu0 : κ u = i := Fin.castSucc_injective hu
    have hv0 : κ v = j := Fin.castSucc_injective hv
    exact ⟨hLt,u,v,hu0,hv0,hAdj⟩
  · rintro ⟨hLt,u,v,hu,hv,hAdj⟩
    exact ⟨hLt,u,v,by simp [hu],by simp [hv],hAdj⟩

/-- A path starting from an old component and following the newly
extended index cannot enter the new last index. It is exactly an
old path, up to casting every index into the larger finite type. -/
theorem ancestor_castSucc_backward
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphOn W) (κ : W → Fin n)
    (i : Fin n) {j : Fin (n+1)}
    (h : TaggedAmalgam.DependencyAncestor
      (backDependency H (fun v => (κ v).castSucc)) i.castSucc j) :
    ∃ j0 : Fin n, j = j0.castSucc ∧
      TaggedAmalgam.DependencyAncestor (backDependency H κ) i j0 := by
  induction h with
  | root =>
      exact ⟨i,rfl,TaggedAmalgam.DependencyAncestor.root⟩
  | @step u v hu hDep ih =>
      obtain ⟨u0,huEq,hOld⟩ := ih
      have hLt : v.val < u.val := hDep.1
      have hvLt : v.val < n := by
        rw [huEq] at hLt
        have hBound : u0.val < n := u0.isLt
        omega
      let v0 : Fin n := ⟨v.val,hvLt⟩
      have hvEq : v = v0.castSucc := Fin.ext rfl
      have hDep0 : backDependency H κ u0 v0 := by
        apply (backDependency_castSucc_iff H κ u0 v0).mp
        rw [← huEq, ← hvEq]
        exact hDep
      exact ⟨v0,hvEq,TaggedAmalgam.DependencyAncestor.step hOld hDep0⟩

theorem ancestor_castSucc_forward
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphOn W) (κ : W → Fin n)
    {i j : Fin n}
    (h : TaggedAmalgam.DependencyAncestor (backDependency H κ) i j) :
    TaggedAmalgam.DependencyAncestor
      (backDependency H (fun v => (κ v).castSucc)) i.castSucc j.castSucc := by
  induction h with
  | root =>
      exact TaggedAmalgam.DependencyAncestor.root
  | @step u v hu hDep ih =>
      exact TaggedAmalgam.DependencyAncestor.step ih
        ((backDependency_castSucc_iff H κ u v).mpr hDep)

/-- Enlarging the *index type* by one unused final component changes
none of the complete unary values on the original graph. -/
theorem canonicalValue_castSucc
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : GraphOn W) (κ : W → Fin n) (u : W) :
    canonicalValue H (fun v => (κ v).castSucc) u =
      canonicalValue H κ u := by
  classical
  ext v
  rw [mem_canonicalValue_iff,mem_canonicalValue_iff]
  constructor
  · intro h
    obtain ⟨j0,hEq,hOld⟩ :=
      ancestor_castSucc_backward H κ (κ u) h
    have hvEq : κ v = j0 := Fin.castSucc_injective hEq
    rw [hvEq]
    exact hOld
  · intro h
    exact ancestor_castSucc_forward H κ h

/-- The entire old unary function is unchanged by freely adding a new
component at the last index, even when the new vertices are joined by
edges to the old vertices. The old graph is induced. -/
theorem canonicalValue_append_old
    (G : GraphOn V)
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (u : {v : V // v ∈ a}) :
    canonicalValue G (appendIndex a κ) u.val =
      (canonicalValue
        (G.pullback (Subtype.val : {v : V // v ∈ a} → V))
        κ u).image (Subtype.val : {v : V // v ∈ a} → V) := by
  classical
  have hClosed : G.IsClosedUnderValues
      (canonicalValue G (appendIndex a κ)) a := by
    have hPrefix := canonicalValue_oldStage_closed G (appendIndex a κ) n
    rw [oldStage_append_old a κ] at hPrefix
    exact hPrefix
  have hRestr := canonicalValue_restrict_image G
    (appendIndex a κ) a hClosed u
  have hIdx : restrictIndex (appendIndex a κ) a =
      (fun v : {v : V // v ∈ a} => (κ v).castSucc) := by
    funext v
    exact appendIndex_old a κ v
  rw [hIdx] at hRestr
  rw [canonicalValue_castSucc] at hRestr
  exact hRestr.symm


/-- If every old indexed stage is empty or minimal strong, and the
entire fresh complement is a minimal strong extension of the old
graph, the extended index retains that exact presentation and
places the fresh block in one new final step. -/
theorem appendIndex_minimal_steps
    (G : GraphOn V)
    (a : Finset V) (κ : {v : V // v ∈ a} → Fin n)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      (G.pullback (Subtype.val : {v : V // v ∈ a} → V)).toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (hNew : G.toPredimension.IsMinimalStrongStep a Finset.univ) :
    ∀ k : ℕ, k < n+1 →
      oldStage (appendIndex a κ) k =
        oldStage (appendIndex a κ) (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage (appendIndex a κ) k)
        (oldStage (appendIndex a κ) (k+1)) := by
  classical
  intro k hk
  by_cases hkOld : k < n
  · rcases hOld k hkOld with hEq | hMin
    · left
      rw [oldStage_append_image a κ k (by omega),
          oldStage_append_image a κ (k+1) (by omega),
          hEq]
    · right
      let H : GraphOn {v : V // v ∈ a} :=
        G.pullback (Subtype.val : {v : V // v ∈ a} → V)
      have hMono : oldStage κ k ⊆ oldStage κ (k+1) := by
        intro v hv
        have hvLt : (κ v).val < k :=
          (mem_oldStage_iff κ k v).mp hv
        exact (mem_oldStage_iff κ (k+1) v).mpr (by omega)
      have hAdj : ∀ u v : {v : V // v ∈ a},
          H.adj u v ↔ G.adj u.val v.val := fun _ _ => Iff.rfl
      have hImage :
          G.toPredimension.IsMinimalStrongStep
            ((oldStage κ k).image (Subtype.val : {v : V // v ∈ a} → V))
            ((oldStage κ (k+1)).image (Subtype.val : {v : V // v ∈ a} → V)) :=
        (H.minimalStrongStep_image_iff G
          (Subtype.val : {v : V // v ∈ a} → V)
          Subtype.val_injective hAdj
          (oldStage κ k) (oldStage κ (k+1)) hMono).mpr hMin
      rw [← oldStage_append_image a κ k (by omega),
          ← oldStage_append_image a κ (k+1) (by omega)] at hImage
      exact hImage
  · have hEq : k = n := by omega
    subst k
    right
    rw [oldStage_append_old a κ, oldStage_final (appendIndex a κ)]
    exact hNew


end FiniteC0
end BigHrushovski
