# Adversarial audit: literal ordered finite old/fresh interval

17 October 2026

## Precise mathematical assertion

Let a and b be disjoint finite subsets of an ordered finite graph
on vertex type V. The type of vertices in a∪b is equivalent to the
disjoint sum of the literal old subtype a and fresh subtype b.
After increasingly enumerating b by Fin(card b), this produces a
canonical ordered-split equivalence

  (a_subtype ⊕ Fin(card b)) ≃ (a∪b)_subtype.

Every old vertex is sent to the *same original vertex of V*
(no isomorphic replacement), and every new ordinal is sent to
the corresponding b-vertex in its inherited order.
Pullback of the complete graph along the equivalence equals
the normalized split graph. This preserves and reflects all
edges and nonedges, including the complete old/fresh boundary.

## Five separately hostile mathematical reviews

1. **Cross-side collisions.** Injectivity of the map to V
is not guaranteed just by injectivity on old and fresh
parts individually. The disjointness hypothesis a∩b=∅
must rule out every old/fresh collision; the proof
uses the certified splitValue_injective theorem.

2. **Onto the right vertex set.** Every vertex of a∪b
must be represented as either an old or fresh summand.
The proof checks surjectivity by a genuine membership
split, rather than replacing the target by an unrelated
isomorphic finite graph.

3. **Exact old labels.** A prescribed embedding of a
into the countable graph must be extended pointwise.
The equivalence's old injection maps ⟨v,hv⟩ back to v,
so transport through the response cannot change the
original old labels.

4. **Fresh order and nonedges.** The fresh subtype
inherits the ambient order on V, and the increasing
Fin(card b) equivalence fixes the intended ordered
local code. The graph equality is a biconditional of
adjacency for every pair, not just preservation
of positive edges.

5. **Still a finite transport.** This theorem only
identifies the split and literal labelled carriers.
It is not the extension property: the existence of
the induced globally d-closed copy comes from the
minimal-diagram response PR #184. The next step is
to transport that response back through this
equivalence, and then iterate minimal steps.

All roles above are internal hostile mathematical
proof-obligation checks, not independent external
referees. Require full Lean CI, standard-axiom
report and placeholder scan before GREEN annotation.
