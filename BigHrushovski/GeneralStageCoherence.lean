import BigHrushovski.NatGraphStage

/-!
# Coherence of finite graphs under arbitrary compatible Nat labellings

The old numerical labels must be literally fixed when a finite
induced extension is transported onto the Nat carrier. This lemma
uses only injectivity and old-label agreement; in particular it
applies both to the original fresh label extension and to the
gap-free initial-segment label extension.

The conclusion reflects nonedges, rather than merely preserving
existing edges. It is the single-step graph coherence invariant
required to assemble a countable sequence of finite strong stages.
-/

namespace BigHrushovski
namespace GraphOn

/-- Two transported finite graph stages agree exactly on the old image
when their induced extension and numeric label data are compatible. -/
theorem transportedToNat_agree_of_label_comp
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : GraphOn A) (K : GraphOn B)
    (i : A → B)
    (hInduced : ∀ a b : A,
      G.adj a b ↔ K.adj (i a) (i b))
    (old : A → ℕ) (hOld : Function.Injective old)
    (new : B → ℕ) (hNew : Function.Injective new)
    (hFixed : ∀ a : A, new (i a) = old a)
    {x y : ℕ}
    (hx : x ∈ (Finset.univ : Finset A).image old)
    (hy : y ∈ (Finset.univ : Finset A).image old) :
    (G.transportedToNat old hOld).adj x y ↔
      (K.transportedToNat new hNew).adj x y := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
  subst x
  subst y
  have hOldAdj := G.transportedToNat_induced old hOld a b
  have hNewAdj := K.transportedToNat_induced new hNew (i a) (i b)
  have hNewAdj' : K.adj (i a) (i b) ↔
      (K.transportedToNat new hNew).adj (old a) (old b) := by
    simpa only [hFixed a, hFixed b] using hNewAdj
  exact hOldAdj.symm.trans ((hInduced a b).trans hNewAdj')

end GraphOn
end BigHrushovski
