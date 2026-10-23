import BigHrushovski.C0TaggedCanonicalIndex

/-!
# The two factor images are unary closed in the actual tagged C0 join

The joined Fin-valued component index keeps the complete left chronology
and appends the right tail. Its backward/same-component paths cannot
leave the left factor: the other tail has higher component indices and
there are no cross-tail graph edges.

A path beginning in the RIGHT factor likewise cannot leave it if the
common named base is closed in the left factor. The only possible
escape would move backwards from a base vertex into an old left tail,
which closedness excludes.

These are concrete finite graph statements. They do not assume that
the factors' complete unary values have already been preserved.
-/

namespace BigHrushovski

namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Closure under all one-step same-component/backedge predecessors
implies closure under the full, transitively generated canonical
vertex-valued unary function. -/
theorem closedUnderCanonicalValue_of_step_closed
    {n : ℕ} (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hStep : ∀ x ∈ s, ∀ y,
      BackOrSame G κ x y → y ∈ s) :
    G.IsClosedUnderValues (canonicalValue G κ) s := by
  intro x hx y hy
  have hReach : VertexReach (BackOrSame G κ) x y :=
    (mem_canonicalValue_iff_vertexReach G κ x y).mp hy
  induction hReach with
  | root => exact hx
  | @next u v hReach hUV ih =>
      exact hStep u ih v hUV

end FiniteC0

namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- An immediate backward/same-component step from a left-tagged
vertex never enters the fresh right tail, without any extra hypothesis. -/
theorem leftTaggedStep_stays_left
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (u : Sum P L) (w : Carrier P L R)
    (h : FiniteC0.BackOrSame (freeGraph G H)
      (joinedIndex κL κR) (leftTag u) w) :
    ∃ v : Sum P L, w = leftTag v := by
  cases w with
  | inl p => exact ⟨.inl p, rfl⟩
  | inr side =>
      cases side with
      | inl l => exact ⟨.inr l, rfl⟩
      | inr r =>
          exfalso
          cases u with
          | inl p =>
              rcases h with hs | ⟨hEdge, hLt⟩
              · have he := congrArg Fin.val hs
                have hb := (κL (.inl p)).isLt
                change (κL (.inl p)).val =
                  n + (κR (.inr r)).val at he
                omega
              · have hb := (κL (.inl p)).isLt
                change n + (κR (.inr r)).val <
                  (κL (.inl p)).val at hLt
                omega
          | inr l =>
              rcases h with hs | ⟨hEdge, hLt⟩
              · have he := congrArg Fin.val hs
                have hb := (κL (.inr l)).isLt
                change (κL (.inr l)).val =
                  n + (κR (.inr r)).val at he
                omega
              · exact (freeGraph_no_cross G H l r) hEdge

/-- The named common base cannot have a backwards/same-component
step into the left tail when it is closed under the complete left
unary function. This is derived from *closedness*, not assumed as
a conclusion about the amalgam. -/
theorem noBackStep_from_closed_left_base
    (G : GraphOn (Sum P L))
    (κL : Sum P L → Fin n)
    (hBaseClosed : G.IsClosedUnderValues
      (FiniteC0.canonicalValue G κL)
      ((Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L)))
    (p : P) (l : L) :
    ¬ FiniteC0.BackOrSame G κL (.inl p) (.inr l) := by
  intro h
  have hp : (Sum.inl p : Sum P L) ∈
      (Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L) :=
    Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  have hv : (Sum.inr l : Sum P L) ∈
      FiniteC0.canonicalValue G κL (.inl p) :=
    (FiniteC0.mem_canonicalValue_iff_vertexReach
      G κL (.inl p) (.inr l)).mpr
      (FiniteC0.VertexReach.next
        FiniteC0.VertexReach.root h)
  have hbad := hBaseClosed (.inl p) hp hv
  obtain ⟨q, _, hEq⟩ := Finset.mem_image.mp hbad
  cases hEq

/-- Every immediate backward step from a right-tagged vertex stays
in that factor. The only nontrivial case is a base vertex pointing
toward an earlier old-left component; left-base closure forbids it. -/
theorem rightTaggedStep_stays_right
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hBaseClosed : G.IsClosedUnderValues
      (FiniteC0.canonicalValue G κL)
      ((Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L)))
    (u : Sum P R) (w : Carrier P L R)
    (h : FiniteC0.BackOrSame (freeGraph G H)
      (joinedIndex κL κR) (rightTag u) w) :
    ∃ v : Sum P R, w = rightTag v := by
  cases w with
  | inl p => exact ⟨.inl p, rfl⟩
  | inr side =>
      cases side with
      | inr r => exact ⟨.inr r, rfl⟩
      | inl l =>
          exfalso
          cases u with
          | inl p =>
              have hLeft : FiniteC0.BackOrSame G κL
                  (.inl p) (.inr l) := by
                rcases h with hs | ⟨hEdge, hLt⟩
                · left
                  apply Fin.ext
                  have he := congrArg Fin.val hs
                  change (κL (.inl p)).val =
                    (κL (.inr l)).val at he
                  exact he
                · right
                  refine ⟨?_, ?_⟩
                  · exact (freeGraph_left G H hAgree
                      (.inl p) (.inr l)).mp hEdge
                  · change (κL (.inr l)).val <
                      (κL (.inl p)).val at hLt
                    exact hLt
              exact noBackStep_from_closed_left_base
                G κL hBaseClosed p l hLeft
          | inr r =>
              rcases h with hs | ⟨hEdge, hLt⟩
              · have he := congrArg Fin.val hs
                have hb := (κL (.inr l)).isLt
                change n + (κR (.inr r)).val =
                  (κL (.inr l)).val at he
                omega
              · have hEdge' :
                    (freeGraph G H).adj
                      (leftTag (.inr l)) (rightTag (.inr r)) :=
                  (freeGraph G H).symm _ _ hEdge
                exact (freeGraph_no_cross G H l r) hEdge'

/-- The full *left* factor image is closed under all canonical unary
values in the tagged amalgam. It cannot acquire any right-tail
component in its transitive unary closure. -/
theorem leftTaggedImage_closed
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m) :
    (freeGraph G H).IsClosedUnderValues
      (FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR))
      ((Finset.univ : Finset (Sum P L)).image
        (leftTag : Sum P L → Carrier P L R)) := by
  apply FiniteC0.closedUnderCanonicalValue_of_step_closed
  intro x hx y hxy
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
  rw [← hu] at hxy
  obtain ⟨v, hv⟩ :=
    leftTaggedStep_stays_left G H κL κR u y hxy
  exact Finset.mem_image.mpr
    ⟨v, Finset.mem_univ _, hv.symm⟩

/-- The full *right* factor image is closed whenever the common base
is closed in the old left factor. This is the only extra closedness
hypothesis needed by the actual free-graph join. -/
theorem rightTaggedImage_closed
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hBaseClosed : G.IsClosedUnderValues
      (FiniteC0.canonicalValue G κL)
      ((Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L))) :
    (freeGraph G H).IsClosedUnderValues
      (FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR))
      ((Finset.univ : Finset (Sum P R)).image
        (rightTag : Sum P R → Carrier P L R)) := by
  apply FiniteC0.closedUnderCanonicalValue_of_step_closed
  intro x hx y hxy
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
  rw [← hu] at hxy
  obtain ⟨v, hv⟩ :=
    rightTaggedStep_stays_right G H hAgree
      κL κR hBaseClosed u y hxy
  exact Finset.mem_image.mpr
    ⟨v, Finset.mem_univ _, hv.symm⟩

end TaggedAmalgam
end BigHrushovski
