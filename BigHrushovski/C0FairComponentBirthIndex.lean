import BigHrushovski.C0FairComponentBirth

/-!
# Track A: the intrinsic chronological index of the fair C₀ components

Each vertex has a unique birth stage in the fair sequence of finite
C₀-closed prefixes. The birth stage is constant precisely on equality
classes of *complete* unary values, and strictly increases from a
strict lower unary dependency to its generator.

On each finite prefix Q_n, the numerical birth stages therefore
define an actual component index into Fin n. No ordering is imposed
inside a component, and no component chronology is assumed a priori.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The unique stage at which the vertex enters the fair sequence. -/
noncomputable def fairComponentBirth
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x : ℕ) : ℕ :=
  Nat.find (fairComponentPrefix_exists_birth C hC x)

theorem fairComponentBirth_spec
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x : ℕ) :
    x ∈ fairComponentPrefix C hC (fairComponentBirth C hC x + 1) \
      fairComponentPrefix C hC (fairComponentBirth C hC x) :=
  Nat.find_spec (fairComponentPrefix_exists_birth C hC x)

/-- Membership in the n-th prefix is exactly birth before n. -/
theorem fairComponentBirth_lt_iff_mem
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n x : ℕ) :
    fairComponentBirth C hC x < n ↔
      x ∈ fairComponentPrefix C hC n := by
  constructor
  · intro h
    exact (fairComponentPrefix_mono C hC
      (fairComponentBirth C hC x + 1) n (by omega))
      (Finset.mem_sdiff.mp (fairComponentBirth_spec C hC x)).1
  · intro hx
    by_contra hlt
    have hn : n ≤ fairComponentBirth C hC x := by omega
    have hOld : x ∈ fairComponentPrefix C hC
        (fairComponentBirth C hC x) :=
      (fairComponentPrefix_mono C hC n
        (fairComponentBirth C hC x) hn) hx
    exact (Finset.mem_sdiff.mp
      (fairComponentBirth_spec C hC x)).2 hOld

/-- Two vertices are born at the same stage if and only if their
complete unary values are equal, including the entire lower closure
and all vertices of their own intrinsic component. -/
theorem fairComponentBirth_eq_iff_value_eq
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x y : ℕ) :
    fairComponentBirth C hC x = fairComponentBirth C hC y ↔
      C x = C y := by
  constructor
  · intro h
    have hx := fairComponentPrefix_new_value C hC
      (fairComponentBirth C hC x) x
      (fairComponentBirth_spec C hC x)
    have hy := fairComponentPrefix_new_value C hC
      (fairComponentBirth C hC y) y
      (fairComponentBirth_spec C hC y)
    rw [← h] at hy
    exact hx.trans hy.symm
  · intro hValue
    let n := fairComponentBirth C hC x
    have hxValue : C x =
        C (leastEnabledVertex C hC (fairComponentPrefix C hC n)) :=
      fairComponentPrefix_new_value C hC n x
        (fairComponentBirth_spec C hC x)
    have hyP : y ∈ unaryComponent C
        (leastEnabledVertex C hC (fairComponentPrefix C hC n)) :=
      (mem_unaryComponent_iff C hC _ y).mpr
        (hValue.symm.trans hxValue)
    have hyNew : y ∈ fairComponentPrefix C hC (n + 1) \
        fairComponentPrefix C hC n := by
      rw [fairComponentPrefix_fresh_component]
      exact hyP
    have hyEq : fairComponentBirth C hC y = n :=
      fairComponentPrefix_birth_unique C hC y
        (fairComponentBirth C hC y) n
        (fairComponentBirth_spec C hC y) hyNew
    exact hyEq.symm

/-- Every strict lower dependency is born before its generator.
The proof uses the complete unary value rather than a direct
old-neighbour approximation. -/
theorem fairComponentBirth_lt_of_strictLower
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    {x y : ℕ} (hy : y ∈ strictLowerValue C x) :
    fairComponentBirth C hC y < fairComponentBirth C hC x := by
  have hOld :=
    fairComponentPrefix_new_lower_old C hC
      (fairComponentBirth C hC x) x
      (fairComponentBirth_spec C hC x) hy
  exact (fairComponentBirth_lt_iff_mem C hC
    (fairComponentBirth C hC x) y).mpr hOld

/-- A vertex in the complete value of x but with a different complete
value has a strictly earlier birth index. -/
theorem fairComponentBirth_lt_of_mem_value_ne
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    {x y : ℕ} (hy : y ∈ C x) (hNe : C y ≠ C x) :
    fairComponentBirth C hC y < fairComponentBirth C hC x := by
  apply fairComponentBirth_lt_of_strictLower C hC
  refine Finset.mem_sdiff.mpr ⟨hy, ?_⟩
  intro hComp
  exact hNe ((mem_unaryComponent_iff C hC x y).mp hComp)

/-- The actual component index on the n-th finite fair prefix.
Because every vertex of that prefix is born before n, the codomain
is the finite ordinal Fin n. Empty prefixes have no vertices. -/
noncomputable def fairComponentBirthIndex
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    {v : ℕ // v ∈ fairComponentPrefix C hC n} → Fin n :=
  fun v => ⟨fairComponentBirth C hC v.val,
    (fairComponentBirth_lt_iff_mem C hC n v.val).mpr v.property⟩

/-- Index-fibre equality means equality of complete unary values,
not merely equal cardinalities or the same immediate old neighbours. -/
theorem fairComponentBirthIndex_eq_iff_value_eq
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ)
    (u v : {w : ℕ // w ∈ fairComponentPrefix C hC n}) :
    fairComponentBirthIndex C hC n u =
      fairComponentBirthIndex C hC n v ↔ C u.val = C v.val := by
  constructor
  · intro h
    have hBirth : fairComponentBirth C hC u.val =
        fairComponentBirth C hC v.val := congrArg Fin.val h
    exact (fairComponentBirth_eq_iff_value_eq C hC u.val v.val).mp
      hBirth
  · intro hValue
    apply Fin.ext
    exact (fairComponentBirth_eq_iff_value_eq C hC u.val v.val).mpr
      hValue

/-- The fair finite index orders complete strict dependencies earlier,
whenever both endpoints belong to the chosen finite prefix. -/
theorem fairComponentBirthIndex_lower_earlier
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ)
    (u v : {w : ℕ // w ∈ fairComponentPrefix C hC n})
    (hv : v.val ∈ C u.val) (hNe : C v.val ≠ C u.val) :
    (fairComponentBirthIndex C hC n v).val <
      (fairComponentBirthIndex C hC n u).val :=
  fairComponentBirth_lt_of_mem_value_ne C hC hv hNe

end FiniteC0
end BigHrushovski
