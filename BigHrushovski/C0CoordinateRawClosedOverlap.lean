import BigHrushovski.C0CoordinateRawHostFiniteClosure
import BigHrushovski.C0CoordinateRawHostFiniteOccurrence

/-!
# Complete finite closed-overlap data for the raw C₀ coordinate host

For finite C-closed sets S,T in the preliminary raw host, their
intersection P is C-closed. The complete C- and J-values on P
are exactly the values inherited from S and T, not only
inclusions. The induced graphs on P from either side agree.
There are no edges between S\\T and T\\S.

These are precisely the overlap and no-cross hypotheses for the
existing two-sided finite functional free-amalgamation theorem.
They do not construct a C₀ presentation of S∪T: transporting the
finite amalgam to that literal union remains a separate step.

All occurrences use complete unary values and graph nonedges;
we do not identify raw vertices by their coordinate labels.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable [DecidableEq RawC0CoordinateVertex]

/-- The induced named unary C-value on the literal finite subtype s.
It is only an induced value for arbitrary s; closedness is the
separate hypothesis ensuring it equals the FULL raw C-value. -/
noncomputable def RawC0CoordinateVertex.valueOn
    (s : Finset RawC0CoordinateVertex) (q : s) : Finset s := by
  classical
  exact (Finset.univ : Finset s).filter
    (fun r : s => r.val ∈ q.val.closedValue)

/-- Membership in an induced value reflects the complete raw
unary incidence without losing negative information. -/
theorem RawC0CoordinateVertex.mem_valueOn_iff
    (s : Finset RawC0CoordinateVertex) (q r : s) :
    r ∈ RawC0CoordinateVertex.valueOn s q ↔
      r.val ∈ q.val.closedValue := by
  classical
  simp [RawC0CoordinateVertex.valueOn]

/-- On a C-closed finite subset, a named induced C-value has
the whole ORIGINAL C-value as its literal image. -/
theorem RawC0CoordinateVertex.valueOn_full_image
    (s : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (q : s) :
    (RawC0CoordinateVertex.valueOn s q).image
      (Subtype.val : s → RawC0CoordinateVertex) =
        q.val.closedValue := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r,hr,hEq⟩ := Finset.mem_image.mp hx
    have hxC : r.val ∈ q.val.closedValue :=
      (RawC0CoordinateVertex.mem_valueOn_iff s q r).mp hr
    simpa only [hEq] using hxC
  · intro hx
    have hxs : x ∈ s := hs q.val q.property x hx
    exact Finset.mem_image.mpr
      ⟨(⟨x,hxs⟩ : s),
        (RawC0CoordinateVertex.mem_valueOn_iff s q ⟨x,hxs⟩).mpr hx,
        rfl⟩

/-- Restricting a COMPLETE named C-value from a larger closed
finite set t to a smaller closed finite set s changes nothing.
This is exact equality of finite values in t, not just inclusion. -/
theorem RawC0CoordinateVertex.valueOn_image_of_closed_subset
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (hst : s ⊆ t)
    (q : s) :
    (RawC0CoordinateVertex.valueOn s q).image
      (fun r : s => (⟨r.val,hst r.property⟩ : t)) =
    RawC0CoordinateVertex.valueOn t
      (⟨q.val,hst q.property⟩ : t) := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨x,hx,hEq⟩ := Finset.mem_image.mp hr
    have hxC : x.val ∈ q.val.closedValue :=
      (RawC0CoordinateVertex.mem_valueOn_iff s q x).mp hx
    have hxr : x.val = r.val := congrArg Subtype.val hEq
    exact (RawC0CoordinateVertex.mem_valueOn_iff
      t ⟨q.val,hst q.property⟩ r).mpr (by
        simpa only [hxr] using hxC)
  · intro hr
    have hrC : r.val ∈ q.val.closedValue :=
      (RawC0CoordinateVertex.mem_valueOn_iff
        t ⟨q.val,hst q.property⟩ r).mp hr
    have hrs : r.val ∈ s := hs q.val q.property r.val hrC
    let x : s := ⟨r.val,hrs⟩
    exact Finset.mem_image.mpr
      ⟨x,(RawC0CoordinateVertex.mem_valueOn_iff s q x).mpr hrC,
        Subtype.ext rfl⟩

/-- The two literal inclusions of the common closed base P=S∩T. -/
def RawC0CoordinateVertex.overlapLeft
    (s t : Finset RawC0CoordinateVertex)
    (q : s ∩ t) : s :=
  ⟨q.val,(Finset.mem_inter.mp q.property).1⟩

def RawC0CoordinateVertex.overlapRight
    (s t : Finset RawC0CoordinateVertex)
    (q : s ∩ t) : t :=
  ⟨q.val,(Finset.mem_inter.mp q.property).2⟩

/-- Complete unary values of the overlap embed EXACTLY onto
the complete unary values inherited from the left factor. -/
theorem RawC0CoordinateVertex.overlap_value_left
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (q : s ∩ t) :
    (RawC0CoordinateVertex.valueOn (s ∩ t) q).image
      (RawC0CoordinateVertex.overlapLeft s t) =
    RawC0CoordinateVertex.valueOn s
      (RawC0CoordinateVertex.overlapLeft s t q) := by
  exact RawC0CoordinateVertex.valueOn_image_of_closed_subset
    (s ∩ t) s
    (RawC0CoordinateVertex.isClosed_inter s t hs ht)
    (Finset.inter_subset_left) q

/-- The same literal, complete unary-value agreement holds for
the right factor, independently of its presentation order. -/
theorem RawC0CoordinateVertex.overlap_value_right
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (q : s ∩ t) :
    (RawC0CoordinateVertex.valueOn (s ∩ t) q).image
      (RawC0CoordinateVertex.overlapRight s t) =
    RawC0CoordinateVertex.valueOn t
      (RawC0CoordinateVertex.overlapRight s t q) := by
  exact RawC0CoordinateVertex.valueOn_image_of_closed_subset
    (s ∩ t) t
    (RawC0CoordinateVertex.isClosed_inter s t hs ht)
    (Finset.inter_subset_right) q

/-- The induced graphs on the overlap have the SAME complete
adjacency and nonadjacency relation from either factor. -/
theorem RawC0CoordinateVertex.overlap_graph_agree
    (s t : Finset RawC0CoordinateVertex)
    (q r : s ∩ t) :
    (rawC0HostGraph.pullback
      (Subtype.val : s → RawC0CoordinateVertex)).adj
        (RawC0CoordinateVertex.overlapLeft s t q)
        (RawC0CoordinateVertex.overlapLeft s t r) ↔
    (rawC0HostGraph.pullback
      (Subtype.val : t → RawC0CoordinateVertex)).adj
        (RawC0CoordinateVertex.overlapRight s t q)
        (RawC0CoordinateVertex.overlapRight s t r) := by
  change rawC0HostGraph.adj q.val r.val ↔
    rawC0HostGraph.adj q.val r.val
  exact Iff.rfl

/-- There are no graph edges between the two exclusive parts
of finite C-closed factors. This is the free graph compatibility
condition needed by the next amalgamation step. -/
theorem RawC0CoordinateVertex.closed_union_noCross
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (q r : RawC0CoordinateVertex)
    (hqs : q ∈ s) (hqt : q ∉ t)
    (hrt : r ∈ t) (hrs : r ∉ s) :
    ¬ rawC0HostGraph.adj q r :=
  rawC0HostGraph_noCross_between s t hs ht
    hqs hqt hrt hrs

end FiniteUnaryCoordinates
end BigHrushovski
