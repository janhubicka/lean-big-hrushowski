import BigHrushovski.CFEmptySelectedBase
import BigHrushovski.CFActualCutAutomaticLift
import BigHrushovski.CFSelectedOldBirthBValues

/-!
# Empty selected old cut at the first represented C_F birth level

For a finite source s and a stage n no later than the birth
level of every vertex of s, its actual stage-n cut is empty.
The ambient full source U_n need not be empty.

Thus there is a unique map from the literal selected old cut
into any prescribed old target stage U_m, even U_0=empty.
We record the exact induced graph, order, full b-value and
strict d-closed-image hypotheses required to apply the
automatic one-level functional lifting theorem.

No total U_n→U_m map, dummy target vertex or increasing
extension to all birth levels is constructed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- If no source vertex was born before n, its literal stage-n
cut is empty even if the complete ambient stage U_n is nonempty. -/
theorem stageCut_empty_of_noEarlierBirth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    stageCut F K s n = ∅ := by
  classical
  ext u
  constructor
  · intro hu
    have hv : toVertex F K n u ∈ s :=
      (mem_stageCut_iff F K s n u).mp hu
    have hLt := toVertex_birth_lt F K n u
    exact False.elim ((not_lt_of_ge (hNoEarlier _ hv)) hLt)
  · intro hu
    exact False.elim (Finset.not_mem_empty u hu)

/-- A selected old source vertex at the first represented level
is impossible, so proofs need not manufacture a target inhabitant. -/
theorem initialCut_noOldVertex
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) : False := by
  have hu := u.property
  rw [stageCut_empty_of_noEarlierBirth F K s n hNoEarlier] at hu
  exact Finset.not_mem_empty u.val hu

/-- The unique map from the actual empty selected old source cut
to any target old stage, including the empty stage. -/
noncomputable def initialCutOldMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier :=
  fun u => False.elim
    (initialCut_noOldVertex F K s n hNoEarlier u)

/-- The unique empty partial old source map preserves and reflects
the actual recursively inherited strict finite-stage order. -/
theorem initialCutOldMap_strictMono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
    StrictMono (initialCutOldMap F K s n m hNoEarlier) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  intro u v huv
  exact False.elim (initialCut_noOldVertex F K s n hNoEarlier u)

/-- The unique empty partial old source map preserves and reflects
all edges and nonedges of the selected old source. -/
theorem initialCutOldMap_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    ∀ u v : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj
          (initialCutOldMap F K s n m hNoEarlier u)
          (initialCutOldMap F K s n m hNoEarlier v) := by
  intro u v
  exact False.elim (initialCut_noOldVertex F K s n hNoEarlier u)

/-- The image of the unique empty partial old map is empty, and
therefore STRICTLY d-closed in the whole target old stage. -/
theorem initialCutOldMap_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n)
        (initialCutOldMap F K s n m hNoEarlier)) Finset.univ := by
  classical
  have hImage : selectedOldImage (stageCut F K s n)
      (initialCutOldMap F K s n m hNoEarlier) = ∅ := by
    ext v
    constructor
    · intro hv
      change v ∈
        ((Finset.univ : Finset
          (SupportCarrier (stage F K n).carrier
            (stageCut F K s n))).image
          (initialCutOldMap F K s n m hNoEarlier)) at hv
      obtain ⟨u, _, _⟩ := Finset.mem_image.mp hv
      exact False.elim (initialCut_noOldVertex F K s n hNoEarlier u)
    · intro hv
      exact False.elim (Finset.not_mem_empty v hv)
  rw [hImage]
  exact empty_dClosed_in_stage F K m

/-- The empty old-source map satisfies the complete actual
birth-b-value induction hypothesis, since there are no old
selected source vertices on which to check it. -/
theorem initialCutOldMap_birthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n m : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    ∀ u : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K m
          (initialCutOldMap F K s n m hNoEarlier w)) =
      birthBValue F K
        (toVertex F K m
          (initialCutOldMap F K s n m hNoEarlier u)) := by
  intro u
  exact False.elim (initialCut_noOldVertex F K s n hNoEarlier u)

end CFCoherentTower
end BigHrushovski
