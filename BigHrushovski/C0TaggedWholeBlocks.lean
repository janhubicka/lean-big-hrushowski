import BigHrushovski.C0ComponentValues

/-!
# Both complete unary values in a tagged finite free amalgam

There are TWO finite types of indices (component blocks and vertices).
The component types are P ⊕ L and P ⊕ R, and the vertex types are
Q ⊕ VL and Q ⊕ VR. Each component indexes its entire finite vertex
fibre, not just a representative.

On the tagged amalgam the complete joined fibre is forced to be the
image of its original fibre. A single equality of the named common
base fibres then gives the fibre-image identities on both factors.

Combining these identities with the previously proved dependency
closure transport gives simultaneous preservation of ALL named
set-valued unary closures, not just graph adjacency or old neighbours.

The remaining interface obligations for the literal C0 finite free
amalgam are now exactly: identified base components, agreement of
the oriented dependency relations on those components, and closure
of the base under dependencies. No function-value conclusion is
postulated in the hypotheses of this theorem.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R Q VL VR : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable [DecidableEq Q] [DecidableEq VL] [DecidableEq VR]

/-- The canonical complete fibre of a component in the tagged join.
For base components the left vertex image is chosen; compatibility
with the right vertex image is a separate equality hypothesis. -/
noncomputable def joinedWholeBlocks
    (blocksL : Sum P L → Finset (Sum Q VL))
    (blocksR : Sum P R → Finset (Sum Q VR)) :
    Carrier P L R → Finset (Carrier Q VL VR)
  | .inl p => (blocksL (.inl p)).image (leftTag : Sum Q VL → Carrier Q VL VR)
  | .inr (.inl l) =>
      (blocksL (.inr l)).image (leftTag : Sum Q VL → Carrier Q VL VR)
  | .inr (.inr r) =>
      (blocksR (.inr r)).image (rightTag : Sum Q VR → Carrier Q VL VR)

/-- Every joined component from the left factor has precisely the
full image of the corresponding left component, without extra vertices. -/
theorem joinedWholeBlocks_left
    (blocksL : Sum P L → Finset (Sum Q VL))
    (blocksR : Sum P R → Finset (Sum Q VR))
    (i : Sum P L) :
    joinedWholeBlocks blocksL blocksR (leftTag i) =
      (blocksL i).image (leftTag : Sum Q VL → Carrier Q VL VR) := by
  cases i <;> rfl

/-- The right joined component is exactly the image of the right
whole block, when shared named component fibres agree on Q. -/
theorem joinedWholeBlocks_right
    (blocksL : Sum P L → Finset (Sum Q VL))
    (blocksR : Sum P R → Finset (Sum Q VR))
    (hBaseBlocks : ∀ p : P,
      (blocksL (.inl p)).image (leftTag : Sum Q VL → Carrier Q VL VR) =
      (blocksR (.inl p)).image (rightTag : Sum Q VR → Carrier Q VL VR))
    (i : Sum P R) :
    joinedWholeBlocks blocksL blocksR (rightTag i) =
      (blocksR i).image (rightTag : Sum Q VR → Carrier Q VL VR) := by
  cases i with
  | inl p => exact hBaseBlocks p
  | inr r => rfl

/-- Both complete unary function values are preserved simultaneously
in the tagged dependency join. The one external compatibility
condition is equality of the complete named base component fibres,
not equality of chronological component orders. -/
theorem freeDependency_wholeClosure_both
    (dL : Sum P L → Sum P L → Prop)
    (dR : Sum P R → Sum P R → Prop)
    (blocksL : Sum P L → Finset (Sum Q VL))
    (blocksR : Sum P R → Finset (Sum Q VR))
    (hAgree : DependencyAgreeBase dL dR)
    (hLClosed : DependencyLeftBaseClosed dL)
    (hRClosed : DependencyRightBaseClosed dR)
    (hBaseBlocks : ∀ p : P,
      (blocksL (.inl p)).image (leftTag : Sum Q VL → Carrier Q VL VR) =
      (blocksR (.inl p)).image (rightTag : Sum Q VR → Carrier Q VL VR)) :
    (∀ root : Sum P L,
      wholeComponentClosure (freeDependency dL dR)
        (joinedWholeBlocks blocksL blocksR) (leftTag root) =
      (wholeComponentClosure dL blocksL root).image
        (leftTag : Sum Q VL → Carrier Q VL VR)) ∧
    (∀ root : Sum P R,
      wholeComponentClosure (freeDependency dL dR)
        (joinedWholeBlocks blocksL blocksR) (rightTag root) =
      (wholeComponentClosure dR blocksR root).image
        (rightTag : Sum Q VR → Carrier Q VL VR)) := by
  constructor
  · intro root
    exact freeDependency_wholeClosure_left
      dL dR blocksL (joinedWholeBlocks blocksL blocksR)
      (leftTag : Sum Q VL → Carrier Q VL VR)
      hAgree hRClosed
      (joinedWholeBlocks_left blocksL blocksR) root
  · intro root
    exact freeDependency_wholeClosure_right
      dL dR blocksR (joinedWholeBlocks blocksL blocksR)
      (rightTag : Sum Q VR → Carrier Q VL VR)
      hAgree hLClosed
      (joinedWholeBlocks_right blocksL blocksR hBaseBlocks) root

end TaggedAmalgam
end BigHrushovski
