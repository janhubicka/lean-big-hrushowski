import BigHrushovski.CFBirthTopBlock
import BigHrushovski.CFRHClosedSubstructures

/-!
# Complete generated-closure values under b-preserving maps

The auxiliary b-function has complete set-valued finite values. A map
which preserves all these values also preserves the *least generated
closure* of every finite set, with equality of the entire images.

One inclusion uses the image of a closed set. For the reverse
inclusion, take the preimage of the target generated closure inside
the finite source generated closure. Exact b-value preservation makes
this finite set b-closed, so minimality forces it to contain the
whole source closure. This proof does not need injectivity.

If a map additionally commutes with the first-root operation, it
carries the full reachable-root set R(v) exactly onto R(f(v)).
For an induced injection, the already validated finite H-naturality
supplies transport of all complete H-values. Root-status reflection
uses injectivity, and is the exact domain condition for the partial
operation H.

The compatibility of the first-root operation with the admissible
order of blocks is kept as an explicit hypothesis. Its derivation
from an order-preserving embedding is a separate outstanding theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Exact transport of least finite generated b-closures for an
arbitrary map preserving complete b-values on the whole generated
source set. No injectivity or graph assumptions are required. -/
theorem birthGeneratedClosure_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (s : Finset (Vertex F K))
    (hB : ∀ v ∈ birthGeneratedClosure F K s,
      (birthBValue F K v).image f = birthBValue F K (f v)) :
    (birthGeneratedClosure F K s).image f =
      birthGeneratedClosure F K (s.image f) := by
  classical
  let C := birthGeneratedClosure F K s
  let D := birthGeneratedClosure F K (s.image f)
  have hCClosed : IsBirthBlockClosed F K C :=
    birthGeneratedClosure_closed F K s
  have hDClosed : IsBirthBlockClosed F K D :=
    birthGeneratedClosure_closed F K (s.image f)
  have hSsubC : s ⊆ C :=
    birthGeneratedClosure_contains F K s
  have hImageClosed : IsBirthBlockClosed F K (C.image f) :=
    birthBlockClosed_image_of_bValues F K f C hCClosed hB
  have hDsubImage : D ⊆ C.image f :=
    birthGeneratedClosure_le_of_closed F K (s.image f) (C.image f)
      (Finset.image_mono f hSsubC) hImageClosed
  let U : Finset (Vertex F K) := C.filter (fun v => f v ∈ D)
  have hUClosed : IsBirthBlockClosed F K U := by
    apply (birthBlockClosed_iff_bValue_subset F K U).mpr
    intro v hv
    obtain ⟨hvC, hfvD⟩ := Finset.mem_filter.mp hv
    have hValueC : birthBValue F K v ⊆ C :=
      birthBValue_subset_of_closed F K C hCClosed hvC
    have hValueD : birthBValue F K (f v) ⊆ D :=
      birthBValue_subset_of_closed F K D hDClosed hfvD
    intro w hw
    have hImage : f w ∈ (birthBValue F K v).image f :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    rw [hB v hvC] at hImage
    exact Finset.mem_filter.mpr ⟨hValueC hw, hValueD hImage⟩
  have hSsubU : s ⊆ U := by
    intro v hv
    apply Finset.mem_filter.mpr
    constructor
    · exact hSsubC hv
    · exact (birthGeneratedClosure_contains F K (s.image f))
        (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have hCsubU : C ⊆ U :=
    birthGeneratedClosure_le_of_closed F K s U hSsubU hUClosed
  have hImageSubD : C.image f ⊆ D := by
    intro w hw
    obtain ⟨v, hvC, hvw⟩ := Finset.mem_image.mp hw
    have hvU : v ∈ U := hCsubU hvC
    have hfvD : f v ∈ D := (Finset.mem_filter.mp hvU).2
    rw [← hvw]
    exact hfvD
  exact le_antisymm hImageSubD hDsubImage

/-- Full image of the first vertices met by a finite set.
This needs only the first-root map to commute with f on that set. -/
theorem rootsOf_image_of_rootMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (s : Finset (Vertex F K))
    (hRoot : ∀ v ∈ s, f (rootOf F K v) = rootOf F K (f v)) :
    (rootsOf F K s).image f = rootsOf F K (s.image f) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp hw
    obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
    have hfw : rootOf F K (f v) = w := by
      calc
        rootOf F K (f v) = f (rootOf F K v) := (hRoot v hv).symm
        _ = f q := by rw [hvq]
        _ = w := hqw
    exact Finset.mem_image.mpr
      ⟨f v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hfw⟩
  · intro hw
    obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp hw
    obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
    have hfw : f (rootOf F K v) = w := by
      calc
        f (rootOf F K v) = rootOf F K (f v) := hRoot v hv
        _ = rootOf F K q := by rw [hvq]
        _ = w := hqw
    exact Finset.mem_image.mpr
      ⟨rootOf F K v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩, hfw⟩

/-- The full reachable root set R(v) transports as a set-valued
function, not merely as an inclusion. -/
theorem birthReachableRoots_image_of_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (hRoot : ∀ v : Vertex F K,
      f (rootOf F K v) = rootOf F K (f v))
    (v : Vertex F K) :
    (birthReachableRoots F K v).image f =
      birthReachableRoots F K (f v) := by
  let C := birthGeneratedClosure F K
    ({v} : Finset (Vertex F K))
  have hCImage :
      C.image f =
        birthGeneratedClosure F K ({f v} : Finset (Vertex F K)) := by
    have h :=
      birthGeneratedClosure_image_of_bValues F K f
        ({v} : Finset (Vertex F K))
        (fun u _ => hB u)
    simpa only [Finset.image_singleton] using h
  change (rootsOf F K C).image f =
    rootsOf F K (birthGeneratedClosure F K ({f v}))
  rw [rootsOf_image_of_rootMap F K f C (fun u _ => hRoot u),
    hCImage]

/-- Recognition of the domain of H is invariant under an
injective map commuting with first-root selection: a vertex
is a first vertex exactly when its image is one. -/
theorem isBirthRoot_iff_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hRoot : ∀ v : Vertex F K,
      f (rootOf F K v) = rootOf F K (f v))
    (v : Vertex F K) :
    IsBirthRoot F K v ↔ IsBirthRoot F K (f v) := by
  change rootOf F K v = v ↔ rootOf F K (f v) = f v
  constructor
  · intro hv
    calc
      rootOf F K (f v) = f (rootOf F K v) := (hRoot v).symm
      _ = f v := by rw [hv]
  · intro hv
    apply hf
    calc
      f (rootOf F K v) = rootOf F K (f v) := hRoot v
      _ = f v := hv

/-- Exact H-value transport for the entire finite vertex domain
under a complete auxiliary b-embedding. In particular it holds
for every *defined* H(S), where S is a finite set of roots. -/
theorem birthDClosedHull_image_of_all_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hAdj : ∀ u v : Vertex F K,
      (countableGraph F K).adj u v ↔
        (countableGraph F K).adj (f u) (f v))
    (hB : ∀ v : Vertex F K,
      (birthBValue F K v).image f = birthBValue F K (f v))
    (s : Finset (Vertex F K)) :
    (birthDClosedHull F K s).image f =
      birthDClosedHull F K (s.image f) :=
  birthDClosedHull_image_of_bValues F K f hf hAdj
    s (birthGeneratedClosure F K s)
    (birthGeneratedClosure_contains F K s)
    (birthGeneratedClosure_closed F K s)
    (fun v _ => hB v)

end CFCoherentTower
end BigHrushovski
