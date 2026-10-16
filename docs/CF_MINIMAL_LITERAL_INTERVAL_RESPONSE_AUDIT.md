# Adversarial audit: a response on the original finite labelled target

17 October 2026

## Exact mathematical statement

Let G be a finite ordered C_F graph, a,b disjoint finite
vertex subsets with a <_d a∪b a minimal strict d-closed
extension, and e:a_subtype→M the *given* globally strictly
d-closed induced old-source embedding into the constructed
countable birth graph M.

The certified minimal-diagram theorem constructs a globally
strictly d-closed induced extension on
a_subtype ⊕ Fin(card b). The explicitly verified ordered
split equivalence E maps this complete carrier *bijectively*
to the original finite target type (a∪b)_subtype, fixing
every old vertex and mapping the new ordinals increasingly
onto the original fresh b vertices.

Define the requested response on the actual target vertices by
  g(x) := h(E^{-1}(x)).
The map is injective, induced (including all nonedges),
satisfies g(x)=e(x) at every original old vertex of a,
and has the same globally strictly d-closed image as h,
since E is surjective. There is no choice of an arbitrary
isomorphic old source or reconstruction of the countable
graph.

The only remaining numerical premise is the exact inverse
domination property of F by K, already constructed under
the published real-growth hypotheses.

## Six separated hostile checks

1. **Literal old source preserved.** The equality
E(Sum.inl x)=⟨x.val,hx⟩ must be proved, so the transported
embedding agrees with e pointwise rather than merely
embedding an isomorphic finite old graph.

2. **No new vertex collisions.** The split equivalence
depends on a∩b=∅ and on injectivity of the increasing
fresh enumeration. Both are required to transport the
injective response to the original target.

3. **Nonedges.** The target inducedness follows from the
complete graph pullback equality through E, not a
forward homomorphism statement. This includes missing
edges across the old/new boundary and inside the
new block.

4. **Global strict d-closure.** The transported map has
exactly the same finite vertex *image* as the verified
split response. The proof explicitly verifies image
equality before transferring global IsGloballyDClosed,
rather than inferring closure from an abstract
bijection of the two vertex types alone.

5. **Only a minimal interval.** The statement requires a
proper minimal strict d-closed inclusion a<_d a∪b.
It does not claim arbitrary weakly strong extensions,
nor imply an unbounded single-step response without
the growth-size hypothesis.

6. **Final finite-chain induction.** The already certified
finite minimal decomposition yields arbitrary d-closed
finite intervals. The last theorem must iterate this
literal one-step response, preserving original labels,
to establish the fully quantified Fraïssé extension
property. This is deliberately kept separate rather
than marking the whole genericity statement GREEN.

All checks are internal hostile mathematical reviews,
not independent external referee agents. Promote an
exact Lean marker only after final integrated CI,
standard axiom report and no-placeholder scan.
