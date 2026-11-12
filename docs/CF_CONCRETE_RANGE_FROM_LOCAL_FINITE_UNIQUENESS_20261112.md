# Track E: concrete complete-support range criterion

12 November 2026. This is a conditional result in the actual
\(\mathcal C_F\) birth presentation, stacked on the finite inverse
lifting work in PR #444. It does not establish the outstanding
finite uniqueness theorem.

## Statement

Write \(C(v)\) for the complete finite b-generated closure of a
vertex \(v\), and \(\sigma(v)\) for the birth levels represented
in \(C(v)\).

Let \(f\) be a self-embedding of the countable ordered auxiliary
b-structure. Assume it preserves the induced graph, the complete
b-values, the birth-level preorder, and the canonical order.
Suppose its birth-level action is a strictly increasing
\(h:\mathbb N\to\mathbb N\).

The **sole additional finite hypothesis** is:

> For every v, any two genuine ordered finite b-embeddings
> of C(v) with the same target birth level for each source
> vertex are equal.

Then the exact range equation holds:

$$
  \operatorname{range}(f)
  =
  \{v:\sigma(v)\subseteq\operatorname{range}(h)\}.
$$

This is the range equation, not the Ellentuck theorem. It applies
to a given global map f; it does not construct a global
level lift from an arbitrary h.

## Proof, in three steps

1. **Forward inclusion.** The existing complete b-value image
   theorem transports C(v) exactly, and so transports
   sigma(v) to h[sigma(v)]. Every point of the image therefore
   has complete support in range(h).
2. **Inverse finite lift.** For a vertex v whose complete
   support lies in range(h), every vertex of the finite
   b-closed set C(v) has birth level in this range.
   PR #444 gives an ordered, induced finite b-embedding
   g:C(v) to M_F with h(pi(gw))=pi(w) on C(v).
3. **Finite uniqueness.** The restriction of the identity map
   to C(v) is an ordered b-embedding. So is f composed with g,
   by the explicit composition theorem. Their output birth
   levels agree. Finite uniqueness gives f(g(w))=w for
   all w in C(v), in particular for w=v.

The proof reuses the abstract range equality theorem
Ellentuck.range_eq_supportDomain_of_finite_lifts. The new work
proves its inclusion and composition premises for the actual
finite b-embedding predicate and discharges the finite inverse
existence premise using Track B.

## Adversarial mathematical review (internal referee roles)

**1. Exact finite language.** The new finite embedding predicate
requires injectivity, induced graph adjacency and nonadjacency,
complete b-values, reflection and preservation of the birth
preorder, and the canonical order. A map carrying only birth
levels correctly is insufficient.

**2. Finite closure.** The source is the entire C(v), not a
singleton or a restricted immediate-neighbour set. The finite
b-closedness of C(v) is proved by the least generated-closure theorem.

**3. Composition.** The b-value equation holds under composition
because the image of a finite set under f composed with g is the
iterated image. All order and adjacency clauses are composed as
equivalences, not one-directional implications.

**4. Inverse levels.** The inverse assignments use a preimage
of h only at birth levels actually represented in C(v).
A global strictly increasing inverse is neither assumed
nor constructed and would generally be impossible.

**5. Uniqueness.** Comparing output birth levels does not by
itself prove the embedding maps equal. This is stated as
the unproved hypothesis hUnique. Its proof requires the full
local request-tag rigidity of Track B (named old support,
block size, complete ordered adjacency matrix, and ordinal).

**6. Relative versus absolute.** A finite partial map is not
assumed to be a countable graph embedding outside its source.
The only global map is the given self-embedding f.

**7. Topology.** The range equation does not identify
point-space approximations with first represented levels,
and does not prove A.1–A.4 or Tychonoff closedness of codes.

**8. Trust.** These are distinct internal mathematical
referee roles, not independent human referee reports.
Exact theorem compilation, standard-axiom inspection,
and placeholder scans are mandatory before validation.

## Remaining

- Prove the single local finite uniqueness hypothesis
  for genuine arbitrary finite ordered R/H embeddings.
- Construct a countable lift for every strictly increasing
  level map with coherent finite restrictions.
- Identify the genuine functional self-embedding space
  with the synthetic supported-domain Ellentuck space.
- Verify the approximation topology and Ramsey-space
  axioms before promoting the manuscript Section 6 marker.

The manuscript is unchanged.
