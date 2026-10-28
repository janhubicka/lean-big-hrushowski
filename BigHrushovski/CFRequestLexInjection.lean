import BigHrushovski.CFRequestMatrixComplete

/-!
# Complete injectivity of the C_F finite request comparison key

A StageRequest consists of a *literal* old support, its strict
d-closedness certificate, and a dependent code specifying the
number of fresh vertices and the full ordered local graph.

The three fields of the lexicographic key recover the whole
request record: the sorted support tuple gives the named support;
the fresh size recovers the Fin index in the bounded catalogue;
the complete row-major adjacency matrix recovers the graph on
the now identical finite local carrier. Remaining certificates
are propositions, hence uniquely determined.

This supplies the missing strict trichotomy of the finite
request comparison. Constructing the inherited linear order
of the countable coherent tower remains a separate step.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]

/-- The complete finite lex key of a local request is injective
on the actual dependent StageRequest records. This is equality
of literal named requests, not equality up to graph isomorphism. -/
theorem requestLexKey_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Function.Injective (requestLexKey G Allowed bound) := by
  classical
  intro r s h
  have hP : r.support = s.support :=
    requestSupportTuple_eq_implies_support G Allowed bound r s
      (congrArg (fun x : List U × (ℕ × List Nat) => x.1) h)
  have hn : r.code.1.val = s.code.1.val :=
    congrArg (fun x : List U × (ℕ × List Nat) => x.2.1) h
  have hbits : requestAdjacencyCode G Allowed bound r =
      requestAdjacencyCode G Allowed bound s :=
    congrArg (fun x : List U × (ℕ × List Nat) => x.2.2) h
  rcases r with ⟨P, hPC, ⟨n, t⟩⟩
  rcases s with ⟨Q, hQC, ⟨m, u⟩⟩
  change P = Q at hP
  subst Q
  have hnm : n = m := Fin.ext hn
  subst m
  let r : StageRequest G Allowed bound := ⟨P, hPC, ⟨n, t⟩⟩
  have hgraphs : t.graph = u.graph := by
    apply requestLocalGraphCode_injective G Allowed bound r
    simpa only [requestAdjacencyCode, requestLocalCoordinates] using hbits
  cases t with
  | mk tGraph tBase tAllowed tMin tSupport =>
    cases u with
    | mk uGraph uBase uAllowed uMin uSupport =>
      cases hgraphs
      rfl

/-- The exact finite request comparison has strict trichotomy:
any two different requests have a definite order determined
by their literal support tuples and complete ordered graph keys. -/
theorem requestLexLt_trichotomy
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound) :
    RequestLexLt G Allowed bound r s ∨ r = s ∨
      RequestLexLt G Allowed bound s r := by
  classical
  rcases lt_trichotomy
      (requestSupportTuple G Allowed bound r)
      (requestSupportTuple G Allowed bound s)
    with hp | hp | hp
  · exact Or.inl (Or.inl hp)
  · rcases lt_trichotomy r.code.1.val s.code.1.val
      with hn | hn | hn
    · exact Or.inl (Or.inr ⟨hp, Or.inl hn⟩)
    · rcases lt_trichotomy
        (requestAdjacencyCode G Allowed bound r)
        (requestAdjacencyCode G Allowed bound s)
        with hb | hb | hb
      · exact Or.inl (Or.inr ⟨hp, Or.inr ⟨hn, hb⟩⟩)
      · right
        left
        apply requestLexKey_injective G Allowed bound
        simp [requestLexKey, hp, hn, hb]
      · exact Or.inr (Or.inr
          (Or.inr ⟨hp.symm, Or.inr ⟨hn.symm, hb⟩⟩))
    · exact Or.inr (Or.inr
        (Or.inr ⟨hp.symm, Or.inl hn⟩))
  · exact Or.inr (Or.inr (Or.inl hp))

/-- Each finite old stage has a strict linear ordering of all
its literal request records, using precisely the named-support
tuple, fresh size and full ordered adjacency matrix. -/
theorem requestLexLt_strict_total
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound) (hne : r ≠ s) :
    RequestLexLt G Allowed bound r s ∨
      RequestLexLt G Allowed bound s r := by
  rcases requestLexLt_trichotomy G Allowed bound r s
    with hlt | heq | hgt
  · exact Or.inl hlt
  · exact False.elim (hne heq)
  · exact Or.inr hgt

end CFStageCatalogue
end BigHrushovski
