import BigHrushovski.FiniteBlockSupportRigidity
import BigHrushovski.CFBirthTopBlock

/-!
# Recover the literal named old support of a C_F block from full values

The countable C_F birth presentation defines for a fresh vertex
v=(n,r,i) the complete auxiliary value b(v)=P_r ∪ B_r,
where P_r is the old support and B_r the full new block.

The two sets are disjoint because all members of P_r were born
before n, while every member of B_r has birth index n.
Consequently, any injective map preserving complete b(v)
and carrying B_r ONTO another complete block B_t must send
P_r ONTO the exact target named old support P_t.

This is the intrinsic support-recovery step required before
literal request-tag uniqueness. It does not yet recover the
ordered adjacency matrix or the internal fresh ordinal.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The actual old support and new block of a birth request are
disjoint as sets of literal countable birth-labelled vertices. -/
theorem birthSupport_disjoint_birthBlock
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n) :
    ∀ v ∈ birthSupport F K n r, v ∉ birthBlock F K n r := by
  intro v hvOld hvNew
  have hBefore : v.1 < n :=
    birthSupport_birth_lt F K n r hvOld
  have hAt : v.1 = n :=
    birthBlock_birth_eq F K n r hvNew
  exact (Nat.ne_of_lt hBefore) hAt

/-- Preservation of a complete birth b-value and its WHOLE fresh
block forces equality of the transported literal old supports.
This uses no separately supplied support-map hypothesis.

The function is injective on the whole birth carrier here;
finite-closed-source maps can apply the underlying generic
finite-set lemma directly to their selected subtype carriers. -/
theorem birthSupport_image_of_completeValue_and_block
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ)
    (r : BirthRequest F K n)
    (t : BirthRequest F K m)
    (i : Fin r.code.1.val)
    (j : Fin t.code.1.val)
    (f : Vertex F K → Vertex F K)
    (hf : Function.Injective f)
    (hValue : (birthBValue F K
        (⟨n, ⟨r, i⟩⟩ : Vertex F K)).image f =
      birthBValue F K (⟨m, ⟨t, j⟩⟩ : Vertex F K))
    (hBlock : (birthBlock F K n r).image f =
      birthBlock F K m t) :
    (birthSupport F K n r).image f =
      birthSupport F K m t := by
  have hFull :
      (birthSupport F K n r ∪ birthBlock F K n r).image f =
        birthSupport F K m t ∪ birthBlock F K m t := by
    simpa only [birthBValue_of_fresh] using hValue
  exact completeBlock_supportImage
    (birthSupport F K n r) (birthBlock F K n r)
    (birthSupport F K m t) (birthBlock F K m t)
    f hf
    (birthSupport_disjoint_birthBlock F K n r)
    (birthSupport_disjoint_birthBlock F K m t)
    hFull hBlock

end CFCoherentTower
end BigHrushovski
