import BigHrushovski.CFRequestPartialOrderTransport
import Mathlib.Data.Finset.Sort

/-!
# Increasing support tuples under a partial old-source embedding

A finite level lift embeds only the selected old closed source S,
not the whole old stage. A map f may therefore be strictly increasing
on S but arbitrary outside it. If P ⊆ S, the increasing enumeration
of the literal image f[P] is exactly the pointwise image of the
increasing enumeration of P.

We prove this by restricting f to the finite subtype P, where it
is a genuine order embedding. The resulting sorted-list equality
is independent of the values of f outside P. It supplies the
named-support tuple certificate in the preceding partial request
transport theorem without a global old-stage embedding.

The fresh-size and complete adjacency-matrix certificates are
separate: they require the transported local graph and its ordered
coordinate list.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [LinearOrder U] [DecidableEq U]
variable [LinearOrder V] [DecidableEq V]

/-- Sorting a finite image commutes with a map strictly increasing
on that finite source set, even if the map is not increasing or
injective outside it. -/
theorem sort_image_strictMonoOn
    (P : Finset U) (f : U → V)
    (hf : StrictMonoOn f P) :
    (P.image f).sort (· ≤ ·) =
      (P.sort (· ≤ ·)).map f := by
  classical
  let I := {u : U // u ∈ P}
  let incl : I ↪o U := OrderEmbedding.subtype _
  let g : I ↪o V :=
    OrderEmbedding.ofStrictMono (fun p : I => f p.val) (by
      intro a b hab
      exact hf a.property b.property hab)
  have hInc : ((Finset.univ : Finset I).map incl.toEmbedding) = P := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hx
      change p.val = x at hp
      exact hp ▸ p.property
    · intro hx
      exact Finset.mem_map.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hImg : ((Finset.univ : Finset I).map g.toEmbedding) = P.image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, _, hpy⟩ := Finset.mem_map.mp hy
      change f p.val = y at hpy
      exact Finset.mem_image.mpr ⟨p.val, p.property, hpy⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact Finset.mem_map.mpr
        ⟨⟨x, hx⟩, Finset.mem_univ _, hxy⟩
  have hInclMono : StrictMonoOn (incl : I → U)
      (Finset.univ : Finset I) :=
    fun _ _ _ _ h => incl.strictMono h
  have hGMono : StrictMonoOn (g : I → V)
      (Finset.univ : Finset I) :=
    fun _ _ _ _ h => g.strictMono h
  have hSortIncl :
      ((Finset.univ : Finset I).sort (· ≤ ·)).map (fun p : I => p.val) =
        P.sort (· ≤ ·) := by
    simpa only [hInc] using hInclMono.map_finsetSort
  have hSortG :
      ((Finset.univ : Finset I).sort (· ≤ ·)).map (fun p : I => f p.val) =
        (P.image f).sort (· ≤ ·) := by
    simpa only [hImg] using hGMono.map_finsetSort
  calc
    (P.image f).sort (· ≤ ·) =
        ((Finset.univ : Finset I).sort (· ≤ ·)).map
          (fun p : I => f p.val) := hSortG.symm
    _ = (((Finset.univ : Finset I).sort (· ≤ ·)).map
          (fun p : I => p.val)).map f := by
          simp only [List.map_map]
          rfl
    _ = (P.sort (· ≤ ·)).map f := by rw [hSortIncl]

variable [Fintype U] [Fintype V]

/-- If the target request has the literal image of the source
support, its increasing named support tuple is automatically
the mapped source tuple. No order embedding of the whole old
stage is required. -/
theorem requestSupportTuple_of_namedImageOn
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (hSub : r.support ⊆ S)
    (hSupport : t.support = r.support.image f) :
    requestSupportTuple H AllowedV boundV t =
      (requestSupportTuple G AllowedU boundU r).map f := by
  classical
  change t.support.sort (· ≤ ·) =
    (r.support.sort (· ≤ ·)).map f
  rw [hSupport]
  have hLocal : StrictMonoOn f r.support :=
    fun _ ha _ hb hab => hf (hSub ha) (hSub hb) hab
  exact sort_image_strictMonoOn r.support f hLocal

/-- A literal transported named support, unchanged fresh size,
and unchanged complete adjacency matrix provide the exact
partial-source request transport record. -/
theorem requestCodeTransportOn_of_namedImage
    (G : GraphOn U) (H : GraphOn V)
    (AllowedU : AllowedLocal U) (AllowedV : AllowedLocal V)
    (boundU : Finset U → ℕ) (boundV : Finset V → ℕ)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r : StageRequest G AllowedU boundU)
    (t : StageRequest H AllowedV boundV)
    (hSub : r.support ⊆ S)
    (hSupport : t.support = r.support.image f)
    (hSize : t.code.1.val = r.code.1.val)
    (hAdj : requestAdjacencyCode H AllowedV boundV t =
      requestAdjacencyCode G AllowedU boundU r) :
    RequestCodeTransportOn G H AllowedU AllowedV
      boundU boundV S f r t :=
  ⟨hSub, requestSupportTuple_of_namedImageOn
      G H AllowedU AllowedV boundU boundV
      S f hf r t hSub hSupport, hSize, hAdj⟩

end CFStageCatalogue
end BigHrushovski
