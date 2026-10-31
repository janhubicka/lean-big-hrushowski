import BigHrushovski.CFPartialSupportLex
import BigHrushovski.CFPartialTagNoncollision

/-!
# Full literal request order under a genuinely partial old map

The prescribed old map has domain exactly the selected old source S.
There need not be a total map from the original old carrier U into the
target old carrier V (notably when S = V = ∅ but U is nonempty).

The request order uses, in sequence, the increasing literal support
tuple, fresh block size, and complete ordered adjacency matrix.  The
support-tuple comparison is supplied by CFPartialSupportLex; the size
and the full adjacency code are supplied by the actual partial-domain
request construction.  The argument proves both directions, including
equality and proper-prefix support tuples.

This is a one-level order interface, not yet the finite induction
over represented levels or the embedding-monoid theorem.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The actual named target requests preserve and reflect the precise
manuscript lex order, even when the old-source embedding is partial. -/
theorem selectedGrowthTagSubtype_order_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r s : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    RequestLexLt G (GrowthAllowedLocal F) (fun P => K P.card)
      r.val s.val ↔
    RequestLexLt H (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedGrowthTagSubtype F K G H S e he D h r)
      (selectedGrowthTagSubtype F K G H S e he D h s) := by
  classical
  let T := selectedGrowthTagSubtype F K G H S e he D h
  have hrSupport : (T r).support =
      CFNamedSupport.supportImage S r.val.support
        (h.supports r.val r.property) e :=
    selectedGrowthTagSubtype_support F K G H S e he D h r
  have hsSupport : (T s).support =
      CFNamedSupport.supportImage S s.val.support
        (h.supports s.val s.property) e :=
    selectedGrowthTagSubtype_support F K G H S e he D h s
  have hSupportLt :
      r.val.support.sort (· ≤ ·) < s.val.support.sort (· ≤ ·) ↔
      (T r).support.sort (· ≤ ·) < (T s).support.sort (· ≤ ·) := by
    rw [hrSupport, hsSupport]
    exact supportImage_partial_sort_lt_iff S
      r.val.support s.val.support
      (h.supports r.val r.property)
      (h.supports s.val s.property) e he
  have hSupportLtRev :
      s.val.support.sort (· ≤ ·) < r.val.support.sort (· ≤ ·) ↔
      (T s).support.sort (· ≤ ·) < (T r).support.sort (· ≤ ·) := by
    rw [hrSupport, hsSupport]
    exact supportImage_partial_sort_lt_iff S
      s.val.support r.val.support
      (h.supports s.val s.property)
      (h.supports r.val r.property) e he
  have hSupportEq :
      r.val.support.sort (· ≤ ·) = s.val.support.sort (· ≤ ·) ↔
      (T r).support.sort (· ≤ ·) = (T s).support.sort (· ≤ ·) := by
    constructor
    · intro heq
      rcases lt_trichotomy ((T r).support.sort (· ≤ ·))
          ((T s).support.sort (· ≤ ·)) with hlt | hsame | hgt
      · have hbad := hSupportLt.mpr hlt
        rw [heq] at hbad
        exact False.elim (lt_irrefl _ hbad)
      · exact hsame
      · have hbad := hSupportLtRev.mpr hgt
        rw [heq] at hbad
        exact False.elim (lt_irrefl _ hbad)
    · intro heq
      rcases lt_trichotomy (r.val.support.sort (· ≤ ·))
          (s.val.support.sort (· ≤ ·)) with hlt | hsame | hgt
      · have hbad := hSupportLt.mp hlt
        rw [heq] at hbad
        exact False.elim (lt_irrefl _ hbad)
      · exact hsame
      · have hbad := hSupportLtRev.mp hgt
        rw [heq] at hbad
        exact False.elim (lt_irrefl _ hbad)
  have hrSize : (T r).code.1.val = r.val.code.1.val :=
    selectedGrowthTagSubtype_size F K G H S e he D h r
  have hsSize : (T s).code.1.val = s.val.code.1.val :=
    selectedGrowthTagSubtype_size F K G H S e he D h s
  have hSizeLt :
      r.val.code.1.val < s.val.code.1.val ↔
        (T r).code.1.val < (T s).code.1.val := by
    rw [hrSize, hsSize]
  have hSizeEq :
      r.val.code.1.val = s.val.code.1.val ↔
        (T r).code.1.val = (T s).code.1.val := by
    rw [hrSize, hsSize]
  have hrCode :
      requestAdjacencyCode G (GrowthAllowedLocal F)
        (fun P => K P.card) r.val =
      requestAdjacencyCode H (GrowthAllowedLocal F)
        (fun P => K P.card) (T r) :=
    selectedGrowthTagSubtype_adjacencyCode F K G H S e he D h r
  have hsCode :
      requestAdjacencyCode G (GrowthAllowedLocal F)
        (fun P => K P.card) s.val =
      requestAdjacencyCode H (GrowthAllowedLocal F)
        (fun P => K P.card) (T s) :=
    selectedGrowthTagSubtype_adjacencyCode F K G H S e he D h s
  have hCodeLt :
      requestAdjacencyCode G (GrowthAllowedLocal F)
          (fun P => K P.card) r.val <
        requestAdjacencyCode G (GrowthAllowedLocal F)
          (fun P => K P.card) s.val ↔
      requestAdjacencyCode H (GrowthAllowedLocal F)
          (fun P => K P.card) (T r) <
        requestAdjacencyCode H (GrowthAllowedLocal F)
          (fun P => K P.card) (T s) := by
    rw [← hrCode, ← hsCode]
  dsimp only [RequestLexLt, requestSupportTuple]
  exact or_congr hSupportLt
    (and_congr hSupportEq
      (or_congr hSizeLt (and_congr hSizeEq hCodeLt)))

end CFStageCatalogue
end BigHrushovski
