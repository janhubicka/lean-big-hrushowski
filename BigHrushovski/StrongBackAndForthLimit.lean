import BigHrushovski.FiniteStrongPartialIso

/-!
# Unions of coherent finite strong partial isomorphisms

An increasing sequence of finite strong partial isomorphisms defines
a unique map on every vertex covered by its source domains. If both
finite domains exhaust ℕ, this map is an induced graph equivalence.

This is the limit step of the usual strong back-and-forth proof.
The existence of a sequence meeting all forth and back requirements
is a separate argument using the finite strong extension lemmas.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- A later finite partial isomorphism retains the domains and all
numerical values of an earlier one. -/
def Extends (p q : FiniteStrongPartialIso M N) : Prop :=
  ∃ (hs : p.source ⊆ q.source) (_ht : p.target ⊆ q.target),
    ∀ x : {x : ℕ // x ∈ p.source},
      (q.equiv ⟨x.val, hs x.property⟩).val = (p.equiv x).val

theorem Extends.refl (p : FiniteStrongPartialIso M N) :
    Extends p p := by
  refine ⟨(fun _ hx => hx), (fun _ hx => hx), ?_⟩
  intro x
  rfl

theorem Extends.trans {p q r : FiniteStrongPartialIso M N}
    (hpq : Extends p q) (hqr : Extends q r) :
    Extends p r := by
  obtain ⟨hs, ht, hValues⟩ := hpq
  obtain ⟨hs', ht', hValues'⟩ := hqr
  refine ⟨hs.trans hs', ht.trans ht', ?_⟩
  intro x
  calc
    (r.equiv ⟨x.val, (hs.trans hs') x.property⟩).val =
        (q.equiv ⟨x.val, hs x.property⟩).val :=
      hValues' ⟨x.val, hs x.property⟩
    _ = (p.equiv x).val := hValues x

/-- The extension order is transitive across arbitrary stages. -/
theorem extends_of_le
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) : Extends (p n) (p m) := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact Extends.refl _
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact (ih hle).trans (hStep m)
      · have hn : n = m + 1 := by omega
        subst n
        exact Extends.refl _

theorem source_mono
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) :
    (p n).source ⊆ (p m).source := by
  obtain ⟨hs, _, _⟩ := extends_of_le p hStep hnm
  exact hs

theorem target_mono
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) :
    (p n).target ⊆ (p m).target := by
  obtain ⟨_, ht, _⟩ := extends_of_le p hStep hnm
  exact ht

/-- Values of a partial isomorphism agree exactly at later stages. -/
theorem value_mono
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) {x : ℕ}
    (hx : x ∈ (p n).source) :
    ((p m).equiv ⟨x, source_mono p hStep hnm hx⟩).val =
      ((p n).equiv ⟨x, hx⟩).val := by
  obtain ⟨hs, _, hValues⟩ := extends_of_le p hStep hnm
  exact hValues ⟨x, hx⟩

/-- The value of a source vertex in the infinite union is its value
at any chosen stage containing that vertex. -/
noncomputable def unionToFun
    (p : ℕ → FiniteStrongPartialIso M N)
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (x : ℕ) : ℕ :=
  let n := Classical.choose (hCoverSource x)
  ((p n).equiv ⟨x, Classical.choose_spec (hCoverSource x)⟩).val

/-- No choice of witness stage changes a vertex's union value. -/
theorem union_at_stage
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (n : ℕ) {x : ℕ} (hx : x ∈ (p n).source) :
    unionToFun p hCoverSource x =
      ((p n).equiv ⟨x, hx⟩).val := by
  let j := Classical.choose (hCoverSource x)
  have hj : x ∈ (p j).source :=
    Classical.choose_spec (hCoverSource x)
  have hChosen :
      unionToFun p hCoverSource x =
        ((p j).equiv ⟨x, hj⟩).val := rfl
  rw [hChosen]
  rcases le_total n j with hnj | hjn
  · exact value_mono p hStep hnj hx
  · exact (value_mono p hStep hjn hj).symm

theorem union_injective
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source) :
    Function.Injective (unionToFun p hCoverSource) := by
  intro x y hxy
  obtain ⟨n, hx⟩ := hCoverSource x
  obtain ⟨m, hy⟩ := hCoverSource y
  let k := max n m
  have hxk : x ∈ (p k).source :=
    source_mono p hStep (Nat.le_max_left n m) hx
  have hyk : y ∈ (p k).source :=
    source_mono p hStep (Nat.le_max_right n m) hy
  have hequiv :
      (p k).equiv ⟨x, hxk⟩ = (p k).equiv ⟨y, hyk⟩ := by
    apply Subtype.ext
    calc
      ((p k).equiv ⟨x, hxk⟩).val =
          unionToFun p hCoverSource x :=
        (union_at_stage p hStep hCoverSource k hxk).symm
      _ = unionToFun p hCoverSource y := hxy
      _ = ((p k).equiv ⟨y, hyk⟩).val :=
        union_at_stage p hStep hCoverSource k hyk
  exact congrArg Subtype.val ((p k).equiv.injective hequiv)

theorem union_surjective
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (hCoverTarget : ∀ y : ℕ, ∃ n, y ∈ (p n).target) :
    Function.Surjective (unionToFun p hCoverSource) := by
  intro y
  obtain ⟨n, hy⟩ := hCoverTarget y
  let x := (p n).equiv.symm ⟨y, hy⟩
  refine ⟨x.val, ?_⟩
  rw [union_at_stage p hStep hCoverSource n x.property]
  change ((p n).equiv x).val = y
  simp [x]

theorem union_induced
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (x y : ℕ) :
    M.adj x y ↔
      N.adj (unionToFun p hCoverSource x)
        (unionToFun p hCoverSource y) := by
  obtain ⟨n, hx⟩ := hCoverSource x
  obtain ⟨m, hy⟩ := hCoverSource y
  let k := max n m
  have hxk : x ∈ (p k).source :=
    source_mono p hStep (Nat.le_max_left n m) hx
  have hyk : y ∈ (p k).source :=
    source_mono p hStep (Nat.le_max_right n m) hy
  calc
    M.adj x y ↔
        N.adj ((p k).equiv ⟨x, hxk⟩).val
          ((p k).equiv ⟨y, hyk⟩).val :=
      (p k).induced ⟨x, hxk⟩ ⟨y, hyk⟩
    _ ↔ N.adj (unionToFun p hCoverSource x)
        (unionToFun p hCoverSource y) := by
      rw [union_at_stage p hStep hCoverSource k hxk,
        union_at_stage p hStep hCoverSource k hyk]

/-- The limit of a coherent, two-sided exhaustive partial-isomorphism
chain is a bijection of the actual Nat carriers. -/
noncomputable def unionEquiv
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (hCoverTarget : ∀ y : ℕ, ∃ n, y ∈ (p n).target) : ℕ ≃ ℕ :=
  Equiv.ofBijective (unionToFun p hCoverSource)
    ⟨union_injective p hStep hCoverSource,
      union_surjective p hStep hCoverSource hCoverTarget⟩

/-- The limit equivalence preserves and reflects all graph edges. -/
theorem unionEquiv_induced
    (p : ℕ → FiniteStrongPartialIso M N)
    (hStep : ∀ n, Extends (p n) (p (n + 1)))
    (hCoverSource : ∀ x : ℕ, ∃ n, x ∈ (p n).source)
    (hCoverTarget : ∀ y : ℕ, ∃ n, y ∈ (p n).target)
    (x y : ℕ) :
    M.adj x y ↔
      N.adj (unionEquiv p hStep hCoverSource hCoverTarget x)
        (unionEquiv p hStep hCoverSource hCoverTarget y) :=
  union_induced p hStep hCoverSource x y

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
