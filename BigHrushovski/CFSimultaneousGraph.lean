import BigHrushovski.CFStageCatalogue

/-!
# The actual tagged graph joining all requests at one finite C_F level

The finite catalogue indexes every actual d-closed old support, with
one complete ordered local graph code for every bounded permitted type.

We create a *single common carrier* consisting of the old vertices
together with a disjoint, request-tagged fresh block for every member
of that catalogue. Its graph has all old edges and all local-code edges
but no further edges. Thus different requests cannot be accidentally
identified, even if their supports or ordered local types are isomorphic.

The proof here concerns the explicit finite graph and its adjacency,
not yet strict d-closedness of its entire old stage, nor membership in
the particular growth-function class C_F. Those need subsequent
predimension and free-amalgamation theorems.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The actual finite set of local-extension requests. -/
abbrev Requests (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ) :=
  StageRequest G Allowed bound

/-- A fresh vertex is tagged by its *particular* request and
by its increasing local ordinal label. -/
abbrev FreshCarrier (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ) :=
  Σ r : Requests G Allowed bound, Fin r.code.1.val

/-- One level of the graph has old vertices and disjoint tagged
copies of all new blocks. -/
abbrev LevelCarrier (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ) :=
  Sum U (FreshCarrier G Allowed bound)

noncomputable instance finite_freshCarrier
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Fintype (FreshCarrier G Allowed bound) := by
  classical
  letI : Fintype (Requests G Allowed bound) := Fintype.ofFinite _
  infer_instance

noncomputable instance finite_levelCarrier
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Fintype (LevelCarrier G Allowed bound) := by
  classical
  infer_instance

/-- The old vertices retain their actual names and are not renumbered. -/
def oldTag (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ) :
    U → LevelCarrier G Allowed bound :=
  Sum.inl

/-- Injection of the complete ordered local type for a given
request into its actual copy in the new level. -/
def localTag (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    Sum (SupportCarrier U r.support) (Fin r.code.1.val) →
      LevelCarrier G Allowed bound
  | Sum.inl p => Sum.inl p.val
  | Sum.inr i => Sum.inr ⟨r, i⟩

theorem localTag_injective (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ)
    (r : Requests G Allowed bound) :
    Function.Injective (localTag G Allowed bound r) := by
  intro x y h
  cases x <;> cases y <;> simp_all [localTag]

/-- The actual graph of the full batch has only old edges and
edges belonging to one explicitly tagged local type. No
additional edges are permitted by its definition. -/
noncomputable def levelGraph (G : GraphOn U)
    (Allowed : AllowedLocal U) (bound : Finset U → ℕ) :
    GraphOn (LevelCarrier G Allowed bound) where
  adj x y :=
    (∃ a b : U,
      oldTag G Allowed bound a = x ∧
      oldTag G Allowed bound b = y ∧ G.adj a b) ∨
    (∃ (r : Requests G Allowed bound)
       (a b : Sum (SupportCarrier U r.support) (Fin r.code.1.val)),
      localTag G Allowed bound r a = x ∧
      localTag G Allowed bound r b = y ∧
      r.code.2.graph.adj a b)
  symm := by
    intro x y h
    rcases h with ⟨a, b, hx, hy, hab⟩ |
      ⟨r, a, b, hx, hy, hab⟩
    · exact Or.inl ⟨b, a, hy, hx, G.symm a b hab⟩
    · exact Or.inr ⟨r, b, a, hy, hx,
        r.code.2.graph.symm a b hab⟩
  irrefl := by
    intro x h
    rcases h with ⟨a, b, hx, hy, hab⟩ |
      ⟨r, a, b, hx, hy, hab⟩
    · have heq : a = b := Sum.inl.inj (hx.trans hy.symm)
      subst b
      exact G.irrefl a hab
    · have heq : a = b :=
        localTag_injective G Allowed bound r (hx.trans hy.symm)
      subst b
      exact r.code.2.graph.irrefl a hab

/-- The graph explicitly includes each edge of the old stage. -/
theorem levelGraph_old_edge
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) (u v : U)
    (huv : G.adj u v) :
    (levelGraph G Allowed bound).adj (Sum.inl u) (Sum.inl v) := by
  exact Or.inl ⟨u, v, rfl, rfl, huv⟩

/-- Every edge of an individual local type is present in that
request's tagged copy. -/
theorem levelGraph_local_edge
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : Requests G Allowed bound)
    (u v : Sum (SupportCarrier U r.support) (Fin r.code.1.val))
    (huv : r.code.2.graph.adj u v) :
    (levelGraph G Allowed bound).adj
      (localTag G Allowed bound r u)
      (localTag G Allowed bound r v) := by
  exact Or.inr ⟨r, u, v, rfl, rfl, huv⟩

/-- No edge can join two different fresh request blocks; this is
a theorem about the *actual constructed graph*, not an
unverified no-cross assumption. -/
theorem levelGraph_no_cross_fresh
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : Requests G Allowed bound)
    (hrs : r ≠ s)
    (i : Fin r.code.1.val) (j : Fin s.code.1.val) :
    ¬ (levelGraph G Allowed bound).adj
      (Sum.inr ⟨r, i⟩) (Sum.inr ⟨s, j⟩) := by
  intro h
  rcases h with ⟨a, b, ha, _, _⟩ |
    ⟨t, a, b, ha, hb, _⟩
  · cases ha
  · cases a with
    | inl p => cases ha
    | inr k =>
      cases b with
      | inl p => cases hb
      | inr l =>
        have htr : t = r :=
          congrArg Sigma.fst (Sum.inr.inj ha)
        have hts : t = s :=
          congrArg Sigma.fst (Sum.inr.inj hb)
        exact hrs (htr.symm.trans hts)

end CFStageCatalogue
end BigHrushovski
