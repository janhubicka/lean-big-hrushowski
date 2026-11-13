# Homogeneity of the countable functional C₀ limit

*Proof prepared for the manuscript; validation status: Lean candidates in PRs
#486, #489, #493 and #495. This text is not a new verification
certificate until those exact heads pass the kernel and axiom checks.*

Let ((N,C)) be the countable functional (C_0)-structure constructed
from the cofinal sequence of finite canonical stages. Recall that
(C(x)) is the **complete** finite one-generated unary value of (x).

The construction gives the following facts, which are proved
independently of homogeneity.

1. Every finite set is contained in a finite canonical stage. These
   stages are closed under (C), and their underlying graphs are
   globally strong in (N).
2. Every finite (C)-closed subset is globally strong.
3. **Extension over a closed base:** if (Asubseteq N) is finite
   and (C)-closed, (B) is a finite canonical functional (C_0)
   structure and (i:A	o B) is an embedding preserving all complete
   unary values, then there is an embedding (j:B	o N) with
   (j(i(a))=a) for all (ain A). In particular,
   (C(j(b))=j[C_B(b)]) for every (bin B).

The third statement was established in the dedicated closed-base
extension theorem, using two-sided finite functional amalgamation and
the stage-extension property of the constructed limit. It is stronger
than the original cofinal-stage extension property.

## Proposition

Every isomorphism between two finite (C)-closed substructures of
((N,C)) extends to an automorphism of ((N,C)).

### Proof

Let (p:A	o A') be such an isomorphism and let (xin N).
Choose a finite canonical stage (T) containing (Acup{x}).
The map (p^{-1}:A'	o T) is an embedding of the complete functional
structure on (A') into (T). Indeed, (A) is (C)-closed, the
restriction of (C) to (A) is its entire unary operation, and
(p) preserves these complete values. No compatibility between the
component orders of (A) and (T) is required.

Apply extension over the closed base (A') to (p^{-1}:A'	o T).
This gives an embedding (h:T	o N) such that
(h(p^{-1}(a'))=a') for every (a'in A'). Thus (h) extends (p)
and its domain contains (x).

The image (h[T]) is (C)-closed, since for every (tin T)
we have
\[
    C(h(t))=h[C_T(t)]\subseteq h[T].
\]
Both (T) and (h[T]) are finite (C)-closed substructures and hence
globally strong. Consequently (h:T	o h[T]) is again an isomorphism
of finite closed functional substructures, satisfying precisely the
hypotheses with which we started.

Applying the same argument to the inverse isomorphism extends its
range to contain any prescribed vertex. Alternating these two
extensions gives a sequence
\[
 p=p_0\subseteq p_1\subseteq p_2\subseteq\cdots
\]
whose domains and ranges both exhaust (N). Their union (g) is a
bijection extending (p), and it preserves and reflects adjacency.

It remains to check that (g) preserves the **complete** unary
operation. Fix (ain N), and choose a stage of the back-and-forth
chain whose domain contains (a). That domain is (C)-closed, so it
also contains every member of the finite set (C(a)).
The corresponding finite isomorphism therefore gives
\[
      g[C(a)]=C(g(a)).
\]
This holds for every (a), so (g) is an automorphism of the
functional structure. \(\square\)

## Adversarial checks of the presentation

**Closure is indispensable.** If (A) is not closed under the
*complete* unary function, then (p^{-1}:A'	o T) need not respect
the full unary values, and the new image of (T) need not be a
legitimate base for the next extension.

**No arbitrary map of the finite stage.** The extension theorem fixes
the *named target base* pointwise. This is what ensures
(h\circ p^{-1}=mathrm{id}_{A'}) and hence that (h) extends (p)
pointwise. An unlabelled embedding of (T) would not suffice.

**No hidden graph-only argument.** Each finite embedding is induced
and preserves the complete unary function by *equality of finite
sets*. Reflecting only adjacency or preserving merely direct
old-neighbour sets would not suffice.

**Global strongness is derived.** A finite (C)-closed substructure
is globally strong by the existing canonical-stage theorem. The
proof does not assume that every finite subset of an arbitrary
2-sparse graph is strong.

**The countable step is elementary.** Finiteness of the unary values
allows the complete-function identity to be checked inside a single
finite stage containing the generator. No new closure construction
or counting argument is needed in the back-and-forth limit.

**Boundary.** This proposition concerns the *unordered* functional
structure. The canonical local ordering selected over previously
ordered lower components in the Ramsey expansion is an additional
requirement, and does not follow from this homogeneity result.

The Lean implementation splits the proof into the inverse-base
compatibility lemma (#486), the actual forth step (#489), inversion
and joint steps (#493), and the ordinary closed-substructure
statement (#495). Those dependencies must all pass exact-head
kernel and source audits before the proposition can receive a
validated manuscript marker.
