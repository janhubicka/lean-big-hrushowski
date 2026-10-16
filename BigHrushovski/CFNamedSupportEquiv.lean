import BigHrushovski.CFGrowthClass

/-!
# The literal named support of a prescribed finite induced embedding

Let A be a finite old source and P ⊆ A a designated old
support. Suppose a prescribed induced embedding of A
into a target graph has already been supplied as a map
from the subtype of A.

Its image Q=e[P] is a *literal* subset of the target.
Restriction of the prescribed embedding defines a canonical
equivalence P ≃ Q between the corresponding subtype carriers.
The equivalence is induced on the old graphs and does not
rename any other vertex of A.

This is the missing bridge between the canonical support
extracted from an abstract finite minimal extension and the
actual named support over which the tagged C_F stage
catalogue enumerates its local extension requests.
-/

namespace BigHrushovski
namespace CFNamedSupport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The image of the literal support P⊆A under a prescribed
embedding defined only on the finite source A. -/
noncomputable def supportImage
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W) : Finset W :=
  P.attach.image (fun p => e ⟨p.val, hPA p.property⟩)

/-- The prescribed source map restricted to the subtype of P,
taking values in the actual image subtype Q=e[P]. -/
noncomputable def restrictedSupportMap
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W) :
    {v : V // v ∈ P} →
      {w : W // w ∈ supportImage A P hPA e} :=
  fun p => ⟨e ⟨p.val, hPA p.property⟩,
    Finset.mem_image.mpr ⟨p, Finset.mem_attach P p, rfl⟩⟩

theorem restrictedSupportMap_injective
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W)
    (he : Function.Injective e) :
    Function.Injective (restrictedSupportMap A P hPA e) := by
  intro p q hpq
  apply Subtype.ext
  have heq : e ⟨p.val, hPA p.property⟩ =
      e ⟨q.val, hPA q.property⟩ :=
    congrArg Subtype.val hpq
  exact congrArg Subtype.val (he heq)

/-- Every target vertex of Q=e[P] has an old support
preimage; the subtype-level map is onto. -/
theorem restrictedSupportMap_surjective
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W) :
    Function.Surjective (restrictedSupportMap A P hPA e) := by
  intro q
  obtain ⟨p, _, hpq⟩ :=
    Finset.mem_image.mp q.property
  refine ⟨p, ?_⟩
  apply Subtype.ext
  exact hpq

/-- The canonical equivalence between the abstract support
and its prescribed *literal* image in the target. -/
noncomputable def supportImageEquiv
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W)
    (he : Function.Injective e) :
    {v : V // v ∈ P} ≃
      {w : W // w ∈ supportImage A P hPA e} :=
  Equiv.ofBijective (restrictedSupportMap A P hPA e)
    ⟨restrictedSupportMap_injective A P hPA e he,
      restrictedSupportMap_surjective A P hPA e⟩

@[simp] theorem supportImageEquiv_val
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W)
    (he : Function.Injective e)
    (p : {v : V // v ∈ P}) :
    (supportImageEquiv A P hPA e he p).val =
      e ⟨p.val, hPA p.property⟩ :=
  rfl

/-- An induced embedding of the prescribed source A restricts
to an induced isomorphism between the graph on P and the
graph on its literal image Q=e[P]. -/
theorem supportImageEquiv_induced
    (G : GraphOn V) (H : GraphOn W)
    (A P : Finset V) (hPA : P ⊆ A)
    (e : {v : V // v ∈ A} → W)
    (he : Function.Injective e)
    (hAdj : ∀ p q : {v : V // v ∈ A},
      G.adj p.val q.val ↔ H.adj (e p) (e q))
    (p q : {v : V // v ∈ P}) :
    (G.pullback Subtype.val).adj p q ↔
      (H.pullback Subtype.val).adj
        (supportImageEquiv A P hPA e he p)
        (supportImageEquiv A P hPA e he q) := by
  change G.adj p.val q.val ↔
    H.adj (e ⟨p.val, hPA p.property⟩)
      (e ⟨q.val, hPA q.property⟩)
  exact hAdj ⟨p.val, hPA p.property⟩
    ⟨q.val, hPA q.property⟩

end CFNamedSupport
end BigHrushovski
