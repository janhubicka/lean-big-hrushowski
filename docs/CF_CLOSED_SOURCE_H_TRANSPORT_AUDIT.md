# Adversarial audit — H-value transport on arbitrary closed C_F source sets

22 October 2026

## Precise result

Let X be any (possibly infinite) vertex subset closed under the
complete auxiliary b-operation. Suppose f is a map defined on
the countable carrier, but impose injectivity, induced adjacency
and exact preservation of b(v) **only for vertices of X**. Its
values outside X are irrelevant. Then, for every finite S⊆X,

    f[cl_b(S)] = cl_b(f[S]),
    f[H(S)] = H(f[S]).

The second formula is valid for the mathematical finite d-hull on
all finite sets and in particular for all permitted finite sets
of first vertices on which the partial language operation H is
defined.

## Ten hostile mathematical checks

1. **Infinite source:** X may be infinite; its finite generated
   b-closure T=cl_b(S) stays in X by the previously certified
   finite-cut theorem. No δ(X) is defined.
2. **Partial map localization:** The proof assumes no global
   inducedness or injectivity outside X. A map on a partial
   source subtype can supply precisely these restricted hypotheses.
3. **Complete b-values:** The image of T is b-closed because
   every complete b(v) maps *onto* b(fv), not merely inside it.
4. **Finite global closure:** T and f[T] are finite b-closed and
   thus globally strictly d-closed. Both global H-hulls agree with
   their finite hulls inside these containers.
5. **Inducedness on T:** The only adjacency iff used for the
   predimension transport concerns pairs in T, a subset of X.
6. **Injectivity on T:** The finite d-hull theorem needs only
   pairwise injectivity on T, inherited from X. No total-map
   injection is postulated.
7. **Whole value equality:** The proof derives equality of
   entire finite H-value image sets, not just inclusion.
8. **Partial H-domain:** Although the mathematical hull lemma
   applies to all finite S, this does not enlarge the partial
   H-function domain in the manuscript.
9. **Other direction:** Recovering b-values from R,H on a partial
   source requires the analogous local finite support theorem,
   plus reflected levels and block order. This PR is only the
   b-to-H direction on arbitrary closed X.
10. **Source-subtype packaging:** A literal embedding
   e:{v // v∈X}→Vertex can be handled without choosing an
   unjustified global induced extension; the eventual theorem
   should use finite restrictions of e to the generated closures.
   That packaging and complete H-domain reflection remain open.

Reviews are separate internal hostile mathematical checks, not
independent external referees.
