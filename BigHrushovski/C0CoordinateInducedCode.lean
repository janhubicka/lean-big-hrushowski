import BigHrushovski.C0CoordinatePointedAgeCode

/-!
# Literal pointed subcode equals the code of the induced finite diagram

The finite code of an induced substructure is obtained by restricting
the complete edge/nonedge and unary-incidence matrices to the chosen
coordinate subset. No new ordered carrier is chosen: the induced
carrier is the literal subtype of the original finite vertex set,
and its increasing labelling is the restriction of the old labelling.

The equality of induced incidence codes is purely finite and does not
need unary closedness. Closedness is instead essential to regard the
induced graph and function values as a *functional substructure*.
The finite canonical C₀ hereditary theorem supplies the subsequent
age certificate. This file does not build the countable host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- Restrict an increasing natural-number labelling to a finite
subtype, without renumbering any vertices. -/
noncomputable def restrictedLabel (e : U ↪o ℕ) (s : Finset U) :
    s ↪o ℕ :=
  OrderEmbedding.ofStrictMono
    (fun u : s => e u.val)
    (by
      intro u v h
      exact e.strictMono h)

@[simp] theorem restrictedLabel_apply
    (e : U ↪o ℕ) (s : Finset U) (u : s) :
    restrictedLabel e s u = e u.val := rfl

/-- The literal support of the restricted labelling is the
original coordinate image of the selected finite set. -/
theorem labelSupport_restrictedLabel
    (e : U ↪o ℕ) (s : Finset U) :
    labelSupport (restrictedLabel e s) = s.image e := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, _, h⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨u.val, u.property,
      by simpa only [restrictedLabel_apply] using h⟩
  · intro hx
    obtain ⟨u, hu, h⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨⟨u, hu⟩, Finset.mem_univ _, by
        simpa only [restrictedLabel_apply] using h⟩

/-- Restricting a complete labelled binary incidence matrix to
the coordinates of s is the same as forming the induced relation
on the literal subtype s and then labelling it. This applies to
both graph edges and complete unary-value incidences. -/
private theorem coordinateRelationPairs_restrict
    (R : U → U → Prop) (e : U ↪o ℕ) (s : Finset U)
    (Rsub : s → s → Prop)
    (hR : ∀ u v : s, Rsub u v ↔ R u.val v.val) :
    ((((Finset.univ.product Finset.univ).filter
      (fun p : U × U => R p.1 p.2)).image
      (fun p => (e p.1, e p.2))).filter
      (fun p : ℕ × ℕ => p.1 ∈ s.image e ∧ p.2 ∈ s.image e)) =
    (((Finset.univ.product Finset.univ).filter
      (fun p : s × s => Rsub p.1 p.2)).image
      (fun p => (restrictedLabel e s p.1,
        restrictedLabel e s p.2))) := by
  classical
  ext z
  rcases z with ⟨x,y⟩
  constructor
  · intro hz
    obtain ⟨hParent, hx, hy⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨u,v⟩, hUV, hEq⟩ := Finset.mem_image.mp hParent
    have hRel : R u v := (Finset.mem_filter.mp hUV).2
    have hEU : e u = x := congrArg Prod.fst hEq
    have hEV : e v = y := congrArg Prod.snd hEq
    obtain ⟨u',hu',hU'⟩ := Finset.mem_image.mp hx
    obtain ⟨v',hv',hV'⟩ := Finset.mem_image.mp hy
    have huEq : u = u' := e.injective (hEU.trans hU'.symm)
    have hvEq : v = v' := e.injective (hEV.trans hV'.symm)
    have hRel' : Rsub (⟨u', hu'⟩ : s) (⟨v', hv'⟩ : s) :=
      (hR _ _).mpr (by simpa only [huEq, hvEq] using hRel)
    refine Finset.mem_image.mpr
      ⟨(⟨u', hu'⟩, ⟨v', hv'⟩), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, hRel'⟩
    · change (e u', e v') = (x, y)
      simp [hU', hV']
  · intro hz
    obtain ⟨⟨u,v⟩, hUV, hEq⟩ := Finset.mem_image.mp hz
    have hRel : R u.val v.val :=
      (hR u v).mp (Finset.mem_filter.mp hUV).2
    have hEq' : (e u.val, e v.val) = (x, y) := by
      simpa only [restrictedLabel_apply] using hEq
    have hEU : e u.val = x := congrArg Prod.fst hEq'
    have hEV : e v.val = y := congrArg Prod.snd hEq'
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨(u.val, v.val), ?_, hEq'⟩
      exact Finset.mem_filter.mpr ⟨by simp, hRel⟩
    · exact Finset.mem_image.mpr ⟨u.val, u.property, hEU⟩
    · exact Finset.mem_image.mpr ⟨v.val, v.property, hEV⟩

/-- The complete adjacency matrix of a restricted pointed code is
the complete adjacency matrix of the induced graph on the selected
finite subtype. This also reflects nonedges. -/
theorem coordinateAdjacencyPairs_restrict
    (G : GraphOn U) (e : U ↪o ℕ) (s : Finset U) :
    (coordinateAdjacencyPairs G e).filter
      (fun p : ℕ × ℕ => p.1 ∈ s.image e ∧ p.2 ∈ s.image e) =
    coordinateAdjacencyPairs (restrictGraph G s)
      (restrictedLabel e s) := by
  exact coordinateRelationPairs_restrict G.adj e s
    (restrictGraph G s).adj (fun _ _ => Iff.rfl)

/-- The same equality for all members of every named unary value,
using the literal finite subtype rather than a renumbered carrier. -/
theorem coordinateClosurePairs_restrict
    (C : U → Finset U) (e : U ↪o ℕ) (s : Finset U) :
    (coordinateClosurePairs C e).filter
      (fun p : ℕ × ℕ => p.1 ∈ s.image e ∧ p.2 ∈ s.image e) =
    coordinateClosurePairs (restrictValue C s)
      (restrictedLabel e s) := by
  exact coordinateRelationPairs_restrict (fun u v => v ∈ C u) e s
    (fun u v => v ∈ restrictValue C s u)
    (fun u v => mem_restrictValue_iff C s u v)

/-- The literal code of a finite induced pointed diagram agrees
EXACTLY with restriction of the original complete pointed code.
There is no arbitrary coordinate choice or graph-only shortcut.

If s is not C-closed, the equality is only an induced-code equality;
it does not assert complete preservation of the original values. -/
theorem literalPointedCode_restrict_eq
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (s : Finset U) (u : s) :
    (literalPointedCode G C e u.val).restrictTo (s.image e)
      (coordinateImage_subset_labelSupport e s)
      (e u.val) ((mem_coordinateImage_iff e s u.val).mpr u.property) =
    literalPointedCode (restrictGraph G s) (restrictValue C s)
      (restrictedLabel e s) u := by
  apply LiteralPointedCode.ext
  · exact (labelSupport_restrictedLabel e s).symm
  · rfl
  · exact coordinateAdjacencyPairs_restrict G e s
  · exact coordinateClosurePairs_restrict C e s

end FiniteUnaryCoordinates
end BigHrushovski
