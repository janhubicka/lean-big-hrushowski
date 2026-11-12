import BigHrushovski.CFCompleteLocalCodeTransport

/-!
# Ordered finite supports under genuinely partial maps

A finite C_F level lift need not include a map of the whole old
source stage into the target old stage. In particular, the old
target carrier may be empty. The usual construction of an
order isomorphism of named supports from a TOTAL map on the
old stage is therefore unnecessarily strong for uniqueness.

This elementary lemma constructs the order isomorphism directly
from a strictly increasing map on the selected finite support
whose image is exactly the target support. It also applies to
finite component supports in the C_0 argument; neither graph,
predimension, nor growth-class assumptions appear.

The construction does not postulate any target point outside the
given support, and works when both supports are empty.
-/

namespace BigHrushovski

open CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U] [LinearOrder U]
variable [Fintype V] [DecidableEq V] [LinearOrder V]

/-- An increasing map defined ONLY on the actual finite source
support, with its exact target image, gives an order isomorphism
of the complete named support subtypes. No extension U → V is
required, even when V is empty. -/
noncomputable def finitePartialSupportOrderIso
    (P : Finset U) (Q : Finset V)
    (e : SupportCarrier U P → V)
    (he : StrictMono e)
    (hQ : (Finset.univ : Finset (SupportCarrier U P)).image e = Q) :
    SupportCarrier U P ≃o SupportCarrier V Q := by
  classical
  let g : SupportCarrier U P → SupportCarrier V Q :=
    fun u => ⟨e u, by
      rw [← hQ]
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩
  have hg : StrictMono g := by
    intro u v huv
    exact he huv
  have hSurj : Function.Surjective g := by
    intro q
    have hq : q.val ∈
        (Finset.univ : Finset (SupportCarrier U P)).image e := by
      rw [hQ]
      exact q.property
    obtain ⟨u, _, huq⟩ := Finset.mem_image.mp hq
    exact ⟨u, Subtype.ext huq⟩
  exact OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono g hg) hSurj

/-- The underlying target vertex of the support order isomorphism
is precisely the value of the original partial map. -/
theorem finitePartialSupportOrderIso_val
    (P : Finset U) (Q : Finset V)
    (e : SupportCarrier U P → V)
    (he : StrictMono e)
    (hQ : (Finset.univ : Finset (SupportCarrier U P)).image e = Q)
    (u : SupportCarrier U P) :
    (finitePartialSupportOrderIso P Q e he hQ u).val = e u := rfl

/-- The exact image hypothesis already forces equality of
the finite support cardinalities; it does not require a map
on the whole ambient old stage. -/
theorem finitePartialSupportOrderIso_card
    (P : Finset U) (Q : Finset V)
    (e : SupportCarrier U P → V)
    (he : StrictMono e)
    (hQ : (Finset.univ : Finset (SupportCarrier U P)).image e = Q) :
    P.card = Q.card := by
  classical
  let iso := finitePartialSupportOrderIso P Q e he hQ
  have hCard := Fintype.card_congr iso.toEquiv
  simpa only [Fintype.card_coe] using hCard

end BigHrushovski
