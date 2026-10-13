import BigHrushovski.C0TaggedDependency

/-!
# Full unary values from finite component-dependency closures

A component dependency closure is not itself a unary function value:
the actual C0 function takes the union of the *entire vertex sets* of
all reachable components. This module proves that exact finite
component-to-vertex unfolding commutes with a map preserving the
reachable components and the full vertex set of each component.

The tagged specialisations combine the newly certified dependency
closure transfer with the block-image compatibility requirement.
This is precisely the last finite set-theoretic calculation before
the application to the actual functional C0 amalgamation diagram.

The component-to-vertex compatibility hypotheses are explicit and
must be checked in that concrete application.
-/

namespace BigHrushovski
namespace TaggedAmalgam

/-- The complete vertex-valued unary closure of a component: union of
the full vertex sets of all reachable component indices. -/
noncomputable def wholeComponentClosure {I V : Type*} [Fintype I]
    (d : I → I → Prop) (blocks : I → Finset V) (root : I) :
    Finset V := by
  classical
  exact (dependencyClosure d root).biUnion blocks

/-- If reachable component sets and the full vertex blocks commute
with given injections/maps, so does the complete unary closure. No
disjointness of vertex blocks is needed for this set identity. -/
theorem wholeComponentClosure_transport
    {I J V W : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [DecidableEq W]
    (d : I → I → Prop) (e : J → J → Prop)
    (blocks : I → Finset V) (joinedBlocks : J → Finset W)
    (indexMap : I → J) (vertexMap : V → W) (root : I)
    (hReach : dependencyClosure e (indexMap root) =
      (dependencyClosure d root).image indexMap)
    (hBlocks : ∀ i : I, joinedBlocks (indexMap i) =
      (blocks i).image vertexMap) :
    wholeComponentClosure e joinedBlocks (indexMap root) =
      (wholeComponentClosure d blocks root).image vertexMap := by
  classical
  ext w
  constructor
  · intro hw
    change w ∈ (dependencyClosure e (indexMap root)).biUnion joinedBlocks at hw
    rw [hReach] at hw
    obtain ⟨j, hj, hwBlock⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    subst j
    rw [hBlocks i] at hwBlock
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hwBlock
    exact Finset.mem_image.mpr
      ⟨v, Finset.mem_biUnion.mpr ⟨i, hi, hv⟩, hvw⟩
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    change v ∈ (dependencyClosure d root).biUnion blocks at hv
    obtain ⟨i, hi, hvBlock⟩ := Finset.mem_biUnion.mp hv
    have hIndex : indexMap i ∈ dependencyClosure e (indexMap root) := by
      rw [hReach]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hBlock : w ∈ joinedBlocks (indexMap i) := by
      rw [hBlocks i]
      exact Finset.mem_image.mpr ⟨v, hvBlock, hvw⟩
    change w ∈ (dependencyClosure e (indexMap root)).biUnion joinedBlocks
    exact Finset.mem_biUnion.mpr ⟨indexMap i, hIndex, hBlock⟩

/-- The left factor's *vertex-valued* unary closure is preserved by
a tagged dependency join, provided each complete block is identified
with the image of the original block. -/
theorem freeDependency_wholeClosure_left
    {P L R V W : Type*}
    [Fintype P] [Fintype L] [Fintype R]
    [DecidableEq P] [DecidableEq L] [DecidableEq R]
    [DecidableEq W]
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (blocks : Sum P L → Finset V)
    (joinedBlocks : Carrier P L R → Finset W)
    (vertexMap : V → W)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyRightBaseClosed dR)
    (hBlocks : ∀ i : Sum P L, joinedBlocks (leftTag i) =
      (blocks i).image vertexMap)
    (root : Sum P L) :
    wholeComponentClosure (freeDependency dL dR) joinedBlocks
      (leftTag root) =
    (wholeComponentClosure dL blocks root).image vertexMap := by
  exact wholeComponentClosure_transport
    dL (freeDependency dL dR) blocks joinedBlocks
    (leftTag : Sum P L → Carrier P L R) vertexMap root
    (freeDependency_closure_left dL dR hAgree hClosed root)
    hBlocks

/-- Symmetric vertex-valued closure preservation on the right. -/
theorem freeDependency_wholeClosure_right
    {P L R V W : Type*}
    [Fintype P] [Fintype L] [Fintype R]
    [DecidableEq P] [DecidableEq L] [DecidableEq R]
    [DecidableEq W]
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (blocks : Sum P R → Finset V)
    (joinedBlocks : Carrier P L R → Finset W)
    (vertexMap : V → W)
    (hAgree : DependencyAgreeBase dL dR)
    (hClosed : DependencyLeftBaseClosed dL)
    (hBlocks : ∀ i : Sum P R, joinedBlocks (rightTag i) =
      (blocks i).image vertexMap)
    (root : Sum P R) :
    wholeComponentClosure (freeDependency dL dR) joinedBlocks
      (rightTag root) =
    (wholeComponentClosure dR blocks root).image vertexMap := by
  exact wholeComponentClosure_transport
    dR (freeDependency dL dR) blocks joinedBlocks
    (rightTag : Sum P R → Carrier P L R) vertexMap root
    (freeDependency_closure_right dL dR hAgree hClosed root)
    hBlocks

end TaggedAmalgam
end BigHrushovski
