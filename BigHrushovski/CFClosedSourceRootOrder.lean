import BigHrushovski.CFClosedSourceHTransport

/-!
# First vertices and R-values for embeddings of closed C_F sources

All hypotheses here are restricted to one possibly infinite b-closed
source subset X of the actual countable birth graph. The map f is
not required to be induced, injective, or order preserving outside X.

Complete b-values on X imply exact generated C(v) images there.
Reflection of the birth-level preorder on X then recognizes every
complete birth block as the top level of C(v). Preservation of the
finite ordinal order *inside* these complete blocks identifies
their first vertices.

Thus f preserves full R(v)-values and reflects the root predicate
(the partial domain of H). The previously verified finite H-hull
transport supplies exact H-values on every defined input set
contained in X. This is the b-to-(R,H) direction for a closed
source, with no unverified global extension assumption.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Internal order preservation, required only on blocks of
vertices belonging to an arbitrary closed source set X. -/
def PreservesBirthBlockOrderOn
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (f : Vertex F K → Vertex F K) : Prop :=
  ∀ v ∈ X, ∀ u w : Vertex F K,
    u ∈ birthBlockOf F K v →
    w ∈ birthBlockOf F K v →
    birthOrdinal F K u < birthOrdinal F K w →
    birthOrdinal F K (f u) < birthOrdinal F K (f w)

/-- Reflect equality of birth levels using the preorder
only for pairs in X, not for all vertices of the generic. -/
theorem birthLevelEq_on
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (f : Vertex F K → Vertex F K)
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (u v : Vertex F K) (hu : u ∈ X) (hv : v ∈ X) :
    u.1 = v.1 ↔ (f u).1 = (f v).1 := by
  constructor
  · intro huv
    exact Nat.le_antisymm
      ((hLevel u hu v hv).mp (Nat.le_of_eq huv))
      ((hLevel v hv u hu).mp (Nat.le_of_eq huv.symm))
  · intro huv
    exact Nat.le_antisymm
      ((hLevel u hu v hv).mpr (Nat.le_of_eq huv))
      ((hLevel v hv u hu).mpr (Nat.le_of_eq huv.symm))

/-- A complete birth block of v maps onto the complete block of
f(v), under b-value preservation and the reflected level
preorder *only on the closed source X*. -/
theorem birthBlockOf_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (v : Vertex F K) (hv : v ∈ X) :
    (birthBlockOf F K v).image f =
      birthBlockOf F K (f v) := by
  classical
  let C := birthCValue F K v
  have hCsubX : ∀ w ∈ C, w ∈ X :=
    generatedClosure_subset_closedSet F K X hX ({v}) (by
      intro u hu
      have huv : u = v := by simpa using hu
      subst u
      exact hv)
  have hCImage : C.image f = birthCValue F K (f v) := by
    have h :=
      birthGeneratedClosure_image_on_closedSet F K X hX f hB
        ({v} : Finset (Vertex F K)) (by
          intro u hu
          have huv : u = v := by simpa using hu
          subst u
          exact hv)
    simpa only [birthCValue, Finset.image_singleton] using h
  ext y
  constructor
  · intro hy
    obtain ⟨w, hwB, hwy⟩ := Finset.mem_image.mp hy
    obtain ⟨hwC, hwLevel⟩ :=
      (birthBlockOf_mem_iff F K v w).mp hwB
    have hfyC : y ∈ birthCValue F K (f v) := by
      rw [← hCImage, ← hwy]
      exact Finset.mem_image.mpr ⟨w, hwC, rfl⟩
    have hfyLevel : y.1 = (f v).1 := by
      rw [← hwy]
      exact (birthLevelEq_on F K X f hLevel w v
        (hCsubX w hwC) hv).mp hwLevel
    exact (birthBlockOf_mem_iff F K (f v) y).mpr
      ⟨hfyC, hfyLevel⟩
  · intro hy
    obtain ⟨hyC, hyLevel⟩ :=
      (birthBlockOf_mem_iff F K (f v) y).mp hy
    have hImage : y ∈ C.image f := by
      rw [hCImage]
      exact hyC
    obtain ⟨w, hwC, hwy⟩ := Finset.mem_image.mp hImage
    have hwLevel : w.1 = v.1 :=
      (birthLevelEq_on F K X f hLevel w v
        (hCsubX w hwC) hv).mpr (by
          rw [hwy]
          exact hyLevel)
    exact Finset.mem_image.mpr
      ⟨w, (birthBlockOf_mem_iff F K v w).mpr
        ⟨hwC, hwLevel⟩, hwy⟩

/-- The first vertex of v's block belongs to any b-closed
source containing v, because the entire block is selected. -/
theorem rootOf_mem_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (v : Vertex F K) (hv : v ∈ X) :
    rootOf F K v ∈ X := by
  rcases v with ⟨n, ⟨r, i⟩⟩
  exact (hX n r i hv).1 ⟨0, r.code.2.fresh_pos⟩

/-- Exact images of blocks plus their increasing ordinal order
force the correct first-root images, even for a map which
behaves arbitrarily outside the closed source X. -/
theorem rootOf_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f)
    (v : Vertex F K) (hv : v ∈ X) :
    f (rootOf F K v) = rootOf F K (f v) := by
  classical
  have hBlock :
      (birthBlockOf F K v).image f = birthBlockOf F K (f v) :=
    birthBlockOf_image_on_closedSet F K X hX f hB hLevel v hv
  have hFirst : rootOf F K v ∈ birthBlockOf F K v :=
    rootOf_mem_birthBlockOf F K v
  have hTarget :
      rootOf F K (f v) ∈ (birthBlockOf F K v).image f := by
    rw [hBlock]
    exact rootOf_mem_birthBlockOf F K (f v)
  obtain ⟨w, hwB, hfw⟩ := Finset.mem_image.mp hTarget
  by_cases hwZero : birthOrdinal F K w = 0
  · have hW : w = rootOf F K v :=
      birthOrdinal_zero_eq_root_of_mem F K v w hwB hwZero
    rw [hW] at hfw
    exact hfw
  · have hPositive : 0 < birthOrdinal F K w :=
      Nat.pos_of_ne_zero hwZero
    have hStrict : birthOrdinal F K (f (rootOf F K v)) <
        birthOrdinal F K (f w) :=
      hOrder v hv (rootOf F K v) w hFirst hwB (by
        rw [birthOrdinal_rootOf F K v]
        exact hPositive)
    rw [hfw, birthOrdinal_rootOf F K (f v)] at hStrict
    exact False.elim ((Nat.not_lt_zero _) hStrict)

/-- Under restricted injectivity, first-root status is both
preserved and reflected for each vertex of the closed source. -/
theorem isBirthRoot_iff_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f)
    (v : Vertex F K) (hv : v ∈ X) :
    IsBirthRoot F K v ↔ IsBirthRoot F K (f v) := by
  have hRoot :=
    rootOf_image_on_closedSet F K X hX f hB hLevel hOrder v hv
  change rootOf F K v = v ↔ rootOf F K (f v) = f v
  constructor
  · intro h
    calc
      rootOf F K (f v) = f (rootOf F K v) := hRoot.symm
      _ = f v := by rw [h]
  · intro h
    apply hf (rootOf F K v) (rootOf_mem_closedSet F K X hX v hv) v hv
    calc
      f (rootOf F K v) = rootOf F K (f v) := hRoot
      _ = f v := h

/-- The entire reachable root value R(v) transports exactly
under complete b-value preservation and increasing order on
the blocks of a closed source set. -/
theorem birthReachableRoots_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f)
    (v : Vertex F K) (hv : v ∈ X) :
    (birthReachableRoots F K v).image f =
      birthReachableRoots F K (f v) := by
  let C := birthCValue F K v
  have hCsubX : ∀ w ∈ C, w ∈ X :=
    generatedClosure_subset_closedSet F K X hX ({v}) (by
      intro u hu
      have huv : u = v := by simpa using hu
      subst u
      exact hv)
  have hCImage : C.image f = birthCValue F K (f v) := by
    have h :=
      birthGeneratedClosure_image_on_closedSet F K X hX f hB
        ({v} : Finset (Vertex F K)) (by
          intro u hu
          have huv : u = v := by simpa using hu
          subst u
          exact hv)
    simpa only [birthCValue, Finset.image_singleton] using h
  change (rootsOf F K C).image f =
    rootsOf F K (birthCValue F K (f v))
  rw [rootsOf_image_of_rootMap F K f C
    (fun w hw => rootOf_image_on_closedSet F K X hX f
      hB hLevel hOrder w (hCsubX w hw)), hCImage]

/-- Preservation/reflection of H's partial argument domain on
every finite set of source vertices, including arbitrary
infinite b-closed sources. -/
theorem rootDomain_iff_image_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f)
    (s : Finset (Vertex F K))
    (hs : ∀ v ∈ s, v ∈ X) :
    (∀ v ∈ s, IsBirthRoot F K v) ↔
      (∀ w ∈ s.image f, IsBirthRoot F K w) := by
  constructor
  · intro hRoot w hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    rw [← hvw]
    exact (isBirthRoot_iff_image_on_closedSet F K X hX f hf
      hB hLevel hOrder v (hs v hv)).mp (hRoot v hv)
  · intro hRoot v hv
    apply (isBirthRoot_iff_image_on_closedSet F K X hX f hf
      hB hLevel hOrder v (hs v hv)).mpr
    exact hRoot (f v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Complete b-values imply complete R(v), H(S), and partial
H-domain transport for every embedding of an arbitrary closed
source X, under inducedness/injectivity/order assumptions only
on X. No global induced extension of the source map is postulated. -/
theorem bValues_imply_RHValues_on_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : Set (Vertex F K))
    (hX : IsBirthBlockClosedSet F K X)
    (f : Vertex F K → Vertex F K)
    (hf : ∀ u ∈ X, ∀ v ∈ X, f u = f v → u = v)
    (hAdj : ∀ u ∈ X, ∀ v ∈ X,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hB : ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hLevel : ∀ u ∈ X, ∀ v ∈ X,
      BirthLevelLe F K u v ↔ BirthLevelLe F K (f u) (f v))
    (hOrder : PreservesBirthBlockOrderOn F K X f) :
    (∀ v ∈ X,
      (birthReachableRoots F K v).image f =
        birthReachableRoots F K (f v)) ∧
    (∀ s : Finset (Vertex F K),
      (∀ v ∈ s, v ∈ X) →
      (birthDClosedHull F K s).image f =
        birthDClosedHull F K (s.image f)) ∧
    (∀ s : Finset (Vertex F K),
      (∀ v ∈ s, v ∈ X) →
      ((∀ v ∈ s, IsBirthRoot F K v) ↔
        (∀ v ∈ s.image f, IsBirthRoot F K v))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact birthReachableRoots_image_on_closedSet F K X hX f hB
      hLevel hOrder v hv
  · intro s hs
    exact birthDClosedHull_image_on_closedSet F K X hX
      f hf hAdj hB s hs
  · intro s hs
    exact rootDomain_iff_image_on_closedSet F K X hX f hf
      hB hLevel hOrder s hs

end CFCoherentTower
end BigHrushovski
