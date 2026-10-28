import BigHrushovski.CFRankedBirthOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
# Canonical support and adjacency keys for C_F level requests

The manuscript orders the finitely many requests at a level by:
  (1) the increasing tuple enumerating the named old support;
  (2) the complete adjacency-and-order code of the local extension,
      relative to that support tuple.

For a finite old stage with its inherited linear order, this module
extracts both keys literally from StageRequest records. The old
coordinates of a local graph are sorted by the inherited order;
fresh coordinates are sorted by their chosen Fin ordinal. The
adjacency key contains the entire matrix of this ordered local graph,
including edges within the fresh block and within the old support.

The code here gives the intended lexicographic comparison of request
records at *one finite stage*. Constructing the coherent inherited
linear orders of all stages, assigning compatible integer request
ranks, and identifying the resulting countable birth order remain
separate steps. These keys do not quietly use an arbitrary order.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]

/-- The named old support, as its increasing tuple in the old
stage order. This is the first comparison key in the manuscript. -/
noncomputable def requestSupportTuple
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) : List U := by
  classical
  exact r.support.sort (· ≤ ·)

/-- Coordinates of a local extension ordered as:
the increasing old support, then the ordered fresh vertices.
The chosen finite block order is the natural order on Fin n. -/
noncomputable def requestLocalCoordinates
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    List (Sum (SupportCarrier U r.support) (Fin r.code.1.val)) := by
  classical
  let olds :=
    (Finset.univ : Finset (SupportCarrier U r.support)).sort (· ≤ ·)
  let fresh :=
    (Finset.univ : Finset (Fin r.code.1.val)).sort (· ≤ ·)
  exact olds.map Sum.inl ++ fresh.map Sum.inr

/-- Full adjacency bit matrix, read in the canonical order of
old and fresh coordinates. This retains all internal and
boundary edges; it is not merely the old-neighbour set. -/
noncomputable def requestAdjacencyCode
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) : List Nat := by
  classical
  let xs := requestLocalCoordinates G Allowed bound r
  exact xs.flatMap (fun u =>
    xs.map (fun v => if r.code.2.graph.adj u v then 1 else 0))

/-- The finite request key of the manuscript: first the support
tuple; then the number of fresh vertices and the complete
ordered graph adjacency code. Lexicographic comparison of the
last two fields resolves local types over an identical support. -/
noncomputable def requestLexKey
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    List U × (ℕ × List Nat) :=
  (requestSupportTuple G Allowed bound r,
    (r.code.1.val, requestAdjacencyCode G Allowed bound r))

/-- Equality of increasing support tuples implies equality of
the *literal named supports*. This remains true for supports
of different cardinalities and does not identify isomorphic
or merely order-equivalent subsets of the old stage. -/
theorem requestSupportTuple_eq_implies_support
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound)
    (h : requestSupportTuple G Allowed bound r =
      requestSupportTuple G Allowed bound s) :
    r.support = s.support := by
  classical
  apply Finset.ext
  intro u
  have hu :
      u ∈ (r.support.sort (· ≤ ·)) ↔
        u ∈ (s.support.sort (· ≤ ·)) := by
    change u ∈ requestSupportTuple G Allowed bound r ↔
      u ∈ requestSupportTuple G Allowed bound s
    rw [h]
  simpa only [Finset.mem_sort] using hu

/-- This matches exactly the finite lexicographic request
comparison specified in the manuscript, including the
proper-prefix convention for different support tuples. -/
def RequestLexLt
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound) : Prop :=
  let P := requestSupportTuple G Allowed bound
  let E := requestAdjacencyCode G Allowed bound
  P r < P s ∨
    (P r = P s ∧
      (r.code.1.val < s.code.1.val ∨
        (r.code.1.val = s.code.1.val ∧ E r < E s)))

/-- An earlier support tuple makes a request earlier, regardless
of its fresh size or complete graph code. -/
theorem requestLexLt_of_support_lt
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound)
    (h : requestSupportTuple G Allowed bound r <
      requestSupportTuple G Allowed bound s) :
    RequestLexLt G Allowed bound r s :=
  Or.inl h

/-- At an identical support tuple and fresh size, the request
comparison is exactly the comparison of complete adjacency codes. -/
theorem requestLexLt_same_support_and_size
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound)
    (hP : requestSupportTuple G Allowed bound r =
      requestSupportTuple G Allowed bound s)
    (hn : r.code.1.val = s.code.1.val) :
    RequestLexLt G Allowed bound r s ↔
      requestAdjacencyCode G Allowed bound r <
        requestAdjacencyCode G Allowed bound s := by
  simp [RequestLexLt, hP, hn]

/-- A request does not precede itself. -/
theorem requestLexLt_irrefl
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    ¬ RequestLexLt G Allowed bound r r := by
  simp [RequestLexLt]

/-- The support key is exactly the ordered old support, rather
than an arbitrary finite request enumeration. -/
theorem requestLexKey_support
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    (requestLexKey G Allowed bound r).1 =
      requestSupportTuple G Allowed bound r := rfl

/-- The first part of the local code is the actual size of the
new block, followed by its full ordered adjacency matrix. -/
theorem requestLexKey_fresh_size
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    (requestLexKey G Allowed bound r).2.1 = r.code.1.val := rfl

end CFStageCatalogue
end BigHrushovski
