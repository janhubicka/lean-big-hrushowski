import BigHrushovski.CFBirthLiteralCoordinates

/-!
# Recover literal request data from old supports and birth blocks

The countable C_F carrier remembers both the actual level
and the complete ordered request tag. In uniqueness arguments,
however, the elementary functional invariants are presented
as finite sets of birth-labelled vertices. The statements
below recover the literal stage request data from these sets.

The old named support is recovered from its birth image by
the injective finite-stage inclusion. An entire birth block
at one fixed level determines the full request tag, since it
contains a fresh vertex remembering that exact tag.

These results do not identify a target request from only its
support and fresh cardinality: the complete ordered adjacency
matrix must still be compared.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Equality of old birth supports of two requests at the same
actual level forces equality of their literal named old-stage
supports. Equal cardinality alone would not suffice. -/
theorem birthRequest_support_eq_of_birthSupport_eq
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r t : BirthRequest F K n)
    (h : birthSupport F K n r = birthSupport F K n t) :
    r.support = t.support := by
  rw [birthSupport_eq_stageSupport_image,
      birthSupport_eq_stageSupport_image] at h
  exact Finset.image_injective (toVertex_injective F K n) h

/-- At a fixed actual birth level, equality of *entire* birth
blocks implies equality of the literal request tags. This is
not a uniqueness theorem for arbitrary maps: it compares two
sets already known to coincide. -/
theorem birthRequest_eq_of_birthBlock_eq
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r t : BirthRequest F K n)
    (h : birthBlock F K n r = birthBlock F K n t) :
    r = t := by
  classical
  let i : Fin r.code.1.val := ⟨0, r.code.2.fresh_pos⟩
  have hv :
      (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ birthBlock F K n t := by
    rw [← h]
    change birthRoot F K n r ∈ birthBlock F K n r
    exact birthRoot_mem_block F K n r
  obtain ⟨j, hij⟩ :=
    (mem_birthBlock_iff_exists_ordinal F K n t _).mp hv
  cases hij
  rfl

/-- Equal full birth-block sets at a fixed level have the
same fresh size, as encoded in their literal StageRequest
records. The stronger request equality is proved separately
above and is not needed for this numerical consequence. -/
theorem birthRequest_freshSize_eq_of_birthBlock_eq
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r t : BirthRequest F K n)
    (h : birthBlock F K n r = birthBlock F K n t) :
    r.code.1.val = t.code.1.val := by
  calc
    r.code.1.val = (birthBlock F K n r).card :=
      (birthBlock_card F K n r).symm
    _ = (birthBlock F K n t).card := congrArg Finset.card h
    _ = t.code.1.val := birthBlock_card F K n t

end CFCoherentTower
end BigHrushovski
