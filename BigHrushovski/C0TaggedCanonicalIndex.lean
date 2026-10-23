import BigHrushovski.C0ClosedEmbeddingValues
import BigHrushovski.C0TaggedOrderReconciliation
import BigHrushovski.TaggedAmalgam

/-!
# Actual component index on a tagged finite C0 graph free amalgam

Let the left components have finite indices κL : P ⊕ L → Fin n.
After frontloading the closed base in the right presentation, let
κR : P ⊕ R → Fin m, with every P index earlier than every R index.
Construct the joined index on P ⊕ (L ⊕ R) by leaving the complete
left ranks unchanged and appending the new right ranks after n.

Both factor injections retain component equality. The right
assertion uses only agreement of the intrinsic component partition
of the shared base; common numerical component orders need not
agree. The joined index also preserves all factor EDGE orientations.

These are actual Fin-valued indices for the freeGraph carrier,
not uninterpreted component dependency names.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable {n m : ℕ}

/-- The canonical rank on the actual tagged free-graph vertices:
left unchanged, fresh right components appended after all left ranks. -/
def joinedIndex
    (κL : Sum P L → Fin n)
    (κR : Sum P R → Fin m) :
    Carrier P L R → Fin (n + m)
  | .inl p => ⟨(κL (.inl p)).val, by omega⟩
  | .inr (.inl l) => ⟨(κL (.inr l)).val, by omega⟩
  | .inr (.inr r) => ⟨n + (κR (.inr r)).val, by omega⟩

theorem joinedIndex_left_val
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (u : Sum P L) :
    (joinedIndex κL κR (leftTag u)).val = (κL u).val := by
  cases u <;> rfl

theorem joinedIndex_right_base_val
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (p : P) :
    (joinedIndex κL κR (rightTag (.inl p))).val =
      (κL (.inl p)).val := rfl

theorem joinedIndex_right_tail_val
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (r : R) :
    (joinedIndex κL κR (rightTag (.inr r))).val =
      n + (κR (.inr r)).val := rfl

theorem joinedIndex_rank
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (u : Carrier P L R) :
    (joinedIndex κL κR u).val =
      joinedRank (fun x => (κL x).val)
        (fun x => (κR x).val) n u := by
  cases u with
  | inl p => rfl
  | inr t => cases t <;> rfl

/-- Both complete left component fibres remain equal in the joined
index, with no base-component order alignment needed. -/
theorem joinedIndex_left_component_iff
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (u v : Sum P L) :
    κL u = κL v ↔
      joinedIndex κL κR (leftTag u) =
        joinedIndex κL κR (leftTag v) := by
  constructor
  · intro h
    apply Fin.ext
    rw [joinedIndex_left_val, joinedIndex_left_val]
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [joinedIndex_left_val] using hv

/-- The same holds for the right component fibres once the two
factor presentations induce the SAME base-component equivalence.
The right base need only be chronologically before the right tail. -/
theorem joinedIndex_right_component_iff
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hBaseComponents : ∀ p q : P,
      κL (.inl p) = κL (.inl q) ↔
      κR (.inl p) = κR (.inl q))
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (u v : Sum P R) :
    κR u = κR v ↔
      joinedIndex κL κR (rightTag u) =
        joinedIndex κL κR (rightTag v) := by
  cases u with
  | inl p =>
      cases v with
      | inl q =>
          constructor
          · intro h
            apply Fin.ext
            have heq := (hBaseComponents p q).mpr h
            simpa [joinedIndex_right_base_val] using
              (congrArg Fin.val heq)
          · intro h
            apply (hBaseComponents p q).mp
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa only [joinedIndex_right_base_val] using hv
      | inr r =>
          constructor
          · intro h
            have heq := congrArg Fin.val h
            have hf := hFront p r
            omega
          · intro h
            have heq := congrArg Fin.val h
            have hn := (κL (.inl p)).isLt
            simp only [joinedIndex_right_base_val,
              joinedIndex_right_tail_val] at heq
            omega
  | inr r =>
      cases v with
      | inl p =>
          constructor
          · intro h
            have heq := congrArg Fin.val h
            have hf := hFront p r
            omega
          · intro h
            have heq := congrArg Fin.val h
            have hn := (κL (.inl p)).isLt
            simp only [joinedIndex_right_base_val,
              joinedIndex_right_tail_val] at heq
            omega
      | inr s =>
          constructor
          · intro h
            apply Fin.ext
            have heq := congrArg Fin.val h
            simp only [joinedIndex_right_tail_val]
            omega
          · intro h
            apply Fin.ext
            have heq := congrArg Fin.val h
            simp only [joinedIndex_right_tail_val] at heq
            omega

/-- The joined left factor has the identical orientation of every
graph edge and identical component partitions. -/
theorem joinedIndex_left_edge_orientation
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (u v : Sum P L) :
    ((κL v).val < (κL u).val) ↔
      ((joinedIndex κL κR (leftTag v)).val <
       (joinedIndex κL κR (leftTag u)).val) := by
  rw [joinedIndex_left_val, joinedIndex_left_val]

/-- Right-factor edge orientation is preserved across every old base,
tail or mixed edge, despite possibly different orders on the base. -/
theorem joinedIndex_right_edge_orientation
    (H : GraphOn (Sum P R))
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (hBaseOrient : ∀ p q : P,
      H.adj (.inl p) (.inl q) →
      ((κL (.inl p)).val < (κL (.inl q)).val ↔
       (κR (.inl p)).val < (κR (.inl q)).val))
    (u v : Sum P R) (hEdge : H.adj u v) :
    ((κR v).val < (κR u).val) ↔
      ((joinedIndex κL κR (rightTag v)).val <
       (joinedIndex κL κR (rightTag u)).val) := by
  have hBound : ∀ x : Sum P L, (κL x).val < n :=
    fun x => (κL x).isLt
  have h := joinedRank_right_edge_orientation
    (fun x => (κL x).val) (fun x => (κR x).val) n
    hBound hFront H.adj hBaseOrient
    v u (H.symm u v hEdge)
  rw [← joinedIndex_rank κL κR (rightTag v),
      ← joinedIndex_rank κL κR (rightTag u)] at h
  exact h.symm

end TaggedAmalgam
end BigHrushovski
