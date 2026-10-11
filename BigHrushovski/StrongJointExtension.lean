import BigHrushovski.StrongBackAndForthRecursion
import BigHrushovski.FiniteStrongPartialExtension
import BigHrushovski.StrongBack

/-!
# Joint finite strong back-and-forth steps

The finite strong extension property first supplies a forth extension
of any globally strong partial isomorphism over a prescribed source
vertex. The exact finite-image equivalence packages this map as a
new finite strong partial isomorphism. Reversing the map and repeating
the argument supplies a back extension over a prescribed target
vertex. The composite preserves all original vertex values and
incorporates both vertices.

Together with the already verified coherent-union and recursive
back-and-forth theorems, this proves uniqueness of countable two-sparse
strong generics. The theorem is *not* conditional on an existing
countable isomorphism or a preconstructed joint-step sequence.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- Double inversion fixes a finite partial isomorphism, including
its precise globally strong domains and induced vertex map. -/
private theorem symm_symm_for_extension
    (p : FiniteStrongPartialIso M N) : p.symm.symm = p := by
  cases p
  simp [FiniteStrongPartialIso.symm]

/-- A strong partial isomorphism extends precisely when its inverse
does. The target inclusion is essential for the converse direction. -/
theorem Extends.inverse {p q : FiniteStrongPartialIso M N}
    (hpq : Extends p q) : Extends p.symm q.symm := by
  obtain ⟨hs, ht, hValues⟩ := hpq
  refine ⟨ht, hs, ?_⟩
  intro y
  let x : {x : ℕ // x ∈ p.source} := p.equiv.symm y
  have hImage :
      q.equiv ⟨x.val, hs x.property⟩ =
        ⟨y.val, ht y.property⟩ := by
    apply Subtype.ext
    calc
      (q.equiv ⟨x.val, hs x.property⟩).val =
          (p.equiv x).val := hValues x
      _ = y.val := by
        change (p.equiv (p.equiv.symm y)).val = y.val
        rw [Equiv.apply_symm_apply]
  have hPreimage :
      q.equiv.symm ⟨y.val, ht y.property⟩ =
        ⟨x.val, hs x.property⟩ := by
    apply q.equiv.injective
    simpa using hImage.symm
  exact congrArg Subtype.val hPreimage

/-- The finite strong forth theorem can be packaged with exact old
values as a genuine extension of strong partial isomorphisms. -/
theorem exists_extending_forth
    (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hCoverM : Predimension.FiniteStrongCover M.toPredimension)
    (hExtN : HasStrongExtensionProperty N)
    (p : FiniteStrongPartialIso M N) (v : ℕ) :
    ∃ q : FiniteStrongPartialIso M N,
      Extends p q ∧ v ∈ q.source := by
  obtain ⟨c, hac, hv, hc, g, hg, hIndG, hBase, hGlobalG⟩ :=
    exists_strong_forth M N hSparseM hCoverM hExtN
      p.source p.target p.source_global p.target_global
      p.equiv p.induced v
  obtain ⟨q, hs, hSource, _hTargetEq, ht, hOld⟩ :=
    exists_extension_from_image p c hac hc
      g hg hIndG hBase hGlobalG
  refine ⟨q, ⟨hs, ht, hOld⟩, ?_⟩
  rw [hSource]
  exact hv

/-- A strong back extension is the strong forth operation for the
inverse partial equivalence, then inverted again. -/
theorem exists_extending_back
    (M N : GraphOn ℕ)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCoverN : Predimension.FiniteStrongCover N.toPredimension)
    (hExtM : HasStrongExtensionProperty M)
    (p : FiniteStrongPartialIso M N) (v : ℕ) :
    ∃ q : FiniteStrongPartialIso M N,
      Extends p q ∧ v ∈ q.target := by
  obtain ⟨q, hpq, hv⟩ :=
    exists_extending_forth N M hSparseN hCoverN
      hExtM p.symm v
  refine ⟨q.symm, ?_, hv⟩
  have h := Extends.inverse hpq
  rw [symm_symm_for_extension p] at h
  exact h

/-- For each finite strong partial isomorphism, a finite induced
strong extension incorporates any prescribed vertex in both countable
carriers, without changing its previous values. -/
theorem hasJointSteps_of_strongExtension
    (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCoverM : Predimension.FiniteStrongCover M.toPredimension)
    (hCoverN : Predimension.FiniteStrongCover N.toPredimension)
    (hExtM : HasStrongExtensionProperty M)
    (hExtN : HasStrongExtensionProperty N) :
    HasJointSteps M N := by
  intro k p
  obtain ⟨q, hpq, hkSource⟩ :=
    exists_extending_forth M N hSparseM hCoverM hExtN p k
  obtain ⟨r, hqr, hkTarget⟩ :=
    exists_extending_back M N hSparseN hCoverN hExtM q k
  refine ⟨r, hpq.trans hqr, ?_, hkTarget⟩
  obtain ⟨hs, _, _⟩ := hqr
  exact hs hkSource

/-- The strong age and extension-property hypotheses characterize
the countable two-sparse generic up to induced graph isomorphism. -/
theorem exists_induced_equiv_of_strongExtension
    (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCoverM : Predimension.FiniteStrongCover M.toPredimension)
    (hCoverN : Predimension.FiniteStrongCover N.toPredimension)
    (hExtM : HasStrongExtensionProperty M)
    (hExtN : HasStrongExtensionProperty N) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      M.adj x y ↔ N.adj (e x) (e y) :=
  exists_induced_equiv_of_joint_steps M N hSparseM hSparseN
    (hasJointSteps_of_strongExtension M N hSparseM hSparseN
      hCoverM hCoverN hExtM hExtN)

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
