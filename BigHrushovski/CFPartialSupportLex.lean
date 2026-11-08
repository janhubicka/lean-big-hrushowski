import BigHrushovski.CFPartialTagNoncollision
import BigHrushovski.CFPartialSupportTuple

/-!
# Lexicographic comparison of named support tuples under partial maps

A prescribed finite C_F level lift embeds only the selected old source
S, not the complete source old stage U. The target old carrier may
be empty, so the map e:S→V cannot in general be totalized to U→V.

The source support P⊆S is represented as a literal finite subset
of the subtype S. Sorting this subtype subset and then forgetting
the subtype gives exactly the increasing tuple of P. Sorting its
image under a strictly increasing e gives exactly the increasing
tuple of the literal target support e[P].

Consequently the usual strict lexicographic comparison of two
support tuples (including proper-prefix cases) is preserved and
reflected by e. This is the missing support-tuple comparison
for the actual partial-domain target request order theorem.

The argument is about finite linear orders and literal subsets;
it does not use properties special to predimension or to the
C_F growth function.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- A literal support P⊆S, represented as a finite set of the
selected old source subtype. This does not rename any old vertex. -/
noncomputable def supportInside
    (S P : Finset U) (hP : P ⊆ S) :
    Finset (SupportCarrier U S) :=
  P.attach.image (fun p =>
    (⟨p.val, hP p.property⟩ : SupportCarrier U S))

/-- Forgetting the selected-source subtype recovers exactly the
original literal support, including the empty support. -/
theorem supportInside_image_val
    (S P : Finset U) (hP : P ⊆ S) :
    (supportInside S P hP).image (fun p => p.val) = P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, hqp⟩ := Finset.mem_image.mp hp
    have hqx : q.val = x := by
      calc
        q.val = p.val := congrArg Subtype.val hqp
        _ = x := hpx
    exact hqx ▸ q.property
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(⟨x, hP hx⟩ : SupportCarrier U S), ?_, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(⟨x, hx⟩ : SupportCarrier U P),
        Finset.mem_attach P _, rfl⟩

/-- Applying the actual partial old map to the selected-support
subtype recovers the literal named support image, without a
total map U→V. -/
theorem supportInside_image_partial
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V) :
    (supportInside S P hP).image e =
      CFNamedSupport.supportImage S P hP e := by
  classical
  simp only [supportInside, CFNamedSupport.supportImage,
    Finset.image_image]
  rfl

/-- The increasing tuple of P is the increasing tuple of its
selected-source subtype followed by forgetting the subtype. -/
theorem supportInside_sorted_val
    (S P : Finset U) (hP : P ⊆ S) :
    P.sort (· ≤ ·) =
      ((supportInside S P hP).sort (· ≤ ·)).map
        (fun p : SupportCarrier U S => p.val) := by
  classical
  have hMono : StrictMonoOn
      (fun p : SupportCarrier U S => p.val)
      (supportInside S P hP) := by
    intro a _ b _ hab
    exact hab
  have hSort :=
    sort_image_strictMonoOn (supportInside S P hP)
      (fun p : SupportCarrier U S => p.val) hMono
  rw [supportInside_image_val] at hSort
  exact hSort

/-- Sorting the literal image support is the same as applying
the selected-subtype map to the increasing subtype tuple. -/
theorem supportInside_sorted_partial
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V) (he : StrictMono e) :
    (CFNamedSupport.supportImage S P hP e).sort (· ≤ ·) =
      ((supportInside S P hP).sort (· ≤ ·)).map e := by
  classical
  have hMono : StrictMonoOn e (supportInside S P hP) := by
    intro a _ b _ hab
    exact he hab
  have hSort :=
    sort_image_strictMonoOn (supportInside S P hP) e hMono
  rw [supportInside_image_partial] at hSort
  exact hSort

/-- A strict order embedding of the selected old source preserves
and reflects the literal support-tuple lex order. The proof also
covers supports of different sizes and proper-prefix comparisons,
without assuming a target old vertex exists. -/
theorem supportImage_partial_sort_lt_iff
    (S P Q : Finset U) (hP : P ⊆ S) (hQ : Q ⊆ S)
    (e : SupportCarrier U S → V) (he : StrictMono e) :
    P.sort (· ≤ ·) < Q.sort (· ≤ ·) ↔
      (CFNamedSupport.supportImage S P hP e).sort (· ≤ ·) <
        (CFNamedSupport.supportImage S Q hQ e).sort (· ≤ ·) := by
  classical
  let R := supportInside S P hP
  let T := supportInside S Q hQ
  let incl : SupportCarrier U S ↪o U :=
    OrderEmbedding.ofStrictMono (fun p : SupportCarrier U S => p.val)
      (by intro a b hab; exact hab)
  let emb : SupportCarrier U S ↪o V :=
    OrderEmbedding.ofStrictMono e he
  have hSrc :
      P.sort (· ≤ ·) < Q.sort (· ≤ ·) ↔
        R.sort (· ≤ ·) < T.sort (· ≤ ·) := by
    rw [supportInside_sorted_val S P hP,
      supportInside_sorted_val S Q hQ]
    exact listLt_map_orderEmbedding_iff incl _ _
  have hDst :
      (CFNamedSupport.supportImage S P hP e).sort (· ≤ ·) <
        (CFNamedSupport.supportImage S Q hQ e).sort (· ≤ ·) ↔
        R.sort (· ≤ ·) < T.sort (· ≤ ·) := by
    rw [supportInside_sorted_partial S P hP e he,
      supportInside_sorted_partial S Q hQ e he]
    exact listLt_map_orderEmbedding_iff emb _ _
  exact hSrc.trans hDst.symm

end CFStageCatalogue
end BigHrushovski
