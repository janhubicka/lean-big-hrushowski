# Track E: literal first-n image stages of genuine ordered R/H embeddings

15 November 2026. Clean branch from current main, using the exact-head
CI-passed and merged source of #516, #542, #549, and #571.

## Statement and proof

For the actual countable C_F birth carrier V, write V_<n for the
literal union of the first n birth stages. Write sigma(v) for the
birth levels in the **entire finite b-generated closure** of v, and
U[S] = {v : sigma(v) ⊆ S}.

For every strictly increasing h:ω→ω and every genuine embedding
f:V→V of the **named ordered partial (R,H) expansion** acting by h,
the theorem `orderedRHEmbedding_stageImage_eq_levelPrefix` proves
as an equality of literal vertex sets:

    f[V_<n] = U[h[[0,n)]].

This is stronger than equality of represented levels and is
exactly the finite approximation identity needed by the natural
copy-domain presentation. It holds without an empty-support
request hypothesis when the prescribed action h and the full
functional embedding are already given.

The proof has three independent certified inputs:
1. The countable b/R/H equivalence transports the genuine f to
   an ordered b-embedding with complete values.
2. The exact range theorem says range(f)=U[range(h)].
3. The first-image-level theorem and the independent finite
   supported-prefix identity give
   f[V_<n] = {v∈range(f): birth(v)∈h[[0,n)]] = U[h[[0,n)]].

A second theorem, `orderedRHEmbeddingWithoutAction_stageImage_eq_levelPrefix`,
uses only actual empty-support requests on each birth level
to **recover** a unique strictly increasing level action from
the named birth-level preorder; it supplies the same equality
simultaneously at every n for an arbitrary functional embedding
of the named expansion.

## Adversarial referee panel (internal mathematical checks)

1. **Actual carrier:** All finite stages are the original literal
   birth-labelled subsets, not isomorphic copies.
2. **Complete support:** The final right-hand side uses every
   level of the complete b-generated closure; the birth level
   alone is insufficient.
3. **Partial H:** Conversion from R/H to b is through the
   exact two-sided theorem, preserving R, defined H-values,
   and reflection of the domain of H; pure graph embeddings
   would be insufficient.
4. **Preorder:** The action-free theorem requires the *named*
   birth-level preorder. A reduct without it is not covered.
5. **Strict increase:** Inverting the birth-level action
   requires strict monotonicity; an arbitrary injective h
   does not preserve the order of initial stages.
6. **No hidden singleton hypothesis:** The first theorem
   does **not** need each level to have an empty-support request;
   the action-free version explicitly supplies that premise.
7. **Two inclusions:** The first stage-image theorem handles
   both directions for actual f; the supported-prefix lemma
   handles both inclusions for complete closures. Neither is
   silently weakened to a set of allowable birth levels.
8. **Initial stage and gaps:** The formula includes n=0
   and arbitrarily large gaps in h[ω].
9. **Finite approximations vs topology:** Exact equality of
   finite vertex sets does not alone establish equality of
   topologies, still less of the finer *Ellentuck topology*
   with the product topology; these remain distinct notions.
10. **Trust:** Two named axiom-audit endpoints and dedicated
    exact-head GitHub Actions CI are included. The new
    compound results are candidates until their checks pass.

These referee roles are internal challenges, not external human reports.

## Next integration

On the clean actual-copy point type from clean PR #573,
show that the first-n finite vertex substructure of the canonical
embedding is this U[h[[0,n)]]. Then transport the product
topology of level sets (proved equivalent to finite vertex-stage
observations in #571) to the finite-approximation **metric**
topology, and separately identify the paper's basic Ellentuck
neighborhoods (which impose both refinement and approximation).
Do not equate the Ellentuck topology with the product topology.

No manuscript validation marker is changed in this PR.
