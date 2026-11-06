# Track B adversarial review — intrinsic literal old support

6 November 2026. Role-separated internal hostile reviewers,
not independent human referee reports.

## Mathematical statement

For any C_F birth block at level n, every vertex of its named
old support was born earlier than n, while all vertices of
the fresh block were born exactly at n. Thus the two finite
sets are literally disjoint.

If an injective birth-carrier map sends the FULL b-value
P_r∪B_r onto P_t∪B_t and maps the entire B_r ONTO B_t,
then it automatically maps the old support P_r ONTO P_t.
No independent transported-support premise is needed.

## Hostile reviewer roles

1. **Complete b-value:** one-sided inclusion of b-values is
   insufficient; exact equality is required.
2. **Whole block:** merely mapping vertices into B_t does
   not rule out unused target block vertices; exact
   B_r-image equality is an explicit hypothesis.
3. **Birth disjointness:** P_r vertices have level < n,
   B_r vertices have level n. The proof explicitly invokes
   both verified birth-level lemmas.
4. **Injection:** needed to stop old support vertices from
   colliding with images of fresh block vertices.
5. **Literal labels:** source and target supports are named
   finite subsets of the real birth-labelled graph, not
   isomorphism classes of local extensions.
6. **Target level:** no n≤m condition is assumed; this
   supports finite lifts to earlier target birth levels.
7. **Empty cases:** the generic support lemma is valid for
   empty supports and empty blocks, and the C_F application
   imposes no unnecessary nonempty target-stage hypothesis.
8. **Scope:** this is a theorem for a GLOBAL injective map
   on the birth carrier. In the finite-lifting uniqueness
   proof, an embedding is defined on a finite CLOSED subtype;
   one must apply the generic support lemma there, or
   explicitly justify a suitable extension. Do not assume
   an arbitrary identity-outside extension is globally
   injective.
9. **Remaining code:** even exact support equality alone
   does not force a target request: need preservation of
   fresh size and complete ordered adjacency matrix.
   Existing literal request uniqueness gives the next step.
10. **Kernel:** exact endpoints are checked in standalone
    CheckAxiomsCFTrackBIntrinsicSupport.lean, included
    by merged workflow #310. Full Lean CI and finite
    regressions are mandatory before any green marker.

No manuscript text is changed or final uniqueness/monoid claimed.

## Current-base verification (6 November 2026)

The reusable complete-block finite support lemma was merged
into main in PR #356 (commit 7ede5ed43bcbb0160941d1e037c366c43dd10830),
after full CI run 42219103503 passed. This PR is now based on
current main rather than the obsolete stacked branch; its exact
C_F application still requires its OWN complete CI.
The theorem is stated for globally injective f on the birth
carrier. Its partial closed-source counterpart must be
derived explicitly before using it in finite-lift uniqueness.
