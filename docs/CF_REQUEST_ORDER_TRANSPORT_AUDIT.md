# Adversarial audit: named C_F request order transport

29 October 2026

## Claim

An old-stage order embedding f: U ↪o V transports each finite
named support tuple by applying f pointwise. If a target request
has this support tuple, the same fresh size, and the *complete*
ordered adjacency matrix, its code is the exact transport of
the source request.

For any two such transported pairs, the manuscript's precise
lexicographic comparison is preserved and reflected. There is
at most one target request with a given transported complete key,
and distinct source requests cannot collapse to the same target
request.

## Independent adversarial perspectives

**Order-theoretic referee.** The proof must work for a proper
non-surjective order embedding and supports of different lengths.
In particular, a proper-prefix comparison must remain a
proper-prefix comparison. The recursive proof of list-lex
transport handles empty and nonempty tails separately. An
arbitrary injection, rather than an order embedding, would be
insufficient: swapping two old vertices reverses a comparison.

**Finite-code referee.** The target support is *literal*, not an
abstract isomorphic subset. The code comparison includes both
fresh size and all adjacency bits, including fresh-fresh edges
and nonedges. Equality of degree sequences or of old-neighbour
sets would not determine the request. Uniqueness invokes the
previously kernel-checked injectivity of the complete request key.

**Partial-source referee.** The theorem is stated for an order
embedding of an entire finite carrier U. In the manuscript's finite
level lifting, however, the prescribed map is only defined on the
selected b-closed old source A_{<i}, not on the whole stage U_{t_i}.
If the target level is earlier, U_{s_i} may be smaller than U_{t_i},
so an order embedding of those whole stages need not exist.
**This is a genuine remaining interface obligation**: first
re-present the source request over the selected closed old carrier,
or prove a partial-support transport lemma. It must not be
silently assumed that the current theorem already handles arbitrary
finite level assignments.

**Amalgamation referee.** The result does not construct a target
request. In the actual finite lifting proof, the earlier image
must first be shown d-closed in the target old stage, and the
transported local graph must be admissible and satisfy the
uniform fresh-size bound. Those hypotheses are *not* consequences
of mere order preservation. Moreover, a whole family of
same-level blocks must be assembled simultaneously; applying a
one-block response successively would shift their target levels.

**Lean/API referee.** All eight new statements are added as exact
axiom endpoints, and the full import graph, placeholder scan,
and finite regressions must pass on the same commit. The
finite-support sorting lemma uses the existing Mathlib theorem
for sorting under a strictly monotone embedding, rather than
assuming that Finset enumeration is natural under arbitrary maps.

These are role-separated hostile mathematical checks within
the project, not claims of independent human referees.

## Verification boundary

If CI passes, this certifies the *order comparison and uniqueness*
of transported request tags, conditional on their complete
transport certificates. It does not certify existence of
transported requests, a simultaneous block map, finite unique
level lifting, or the embedding monoid theorem.
