# Track B: induced restriction to an entire local request

12 November 2026. The local carrier contains ALL coordinates of
the named old support and the entire fresh ordinal block. We
prove that an arbitrary finite source map restricts to this
carrier as soon as the finite source is b-closed and contains
one fresh vertex of the request. The inducedness conclusion
is an **iff** on every pair of local coordinates.

## Six independent adversarial referee roles

1. **Closure of the full local carrier.** The source closure
   predicate supplies both halves: every old support birth
   vertex and every fresh ordinal of the chosen request.
   A set containing only the selected fresh vertex would not
   be enough to evaluate the proposed local map.
2. **Literal naming.** Old coordinates are evaluated via
   `toVertex F K n`; fresh coordinates via the literal
   dependent vertex `⟨n,⟨r,j⟩⟩`. There is no auxiliary
   isomorphism or renumbering of the request.
3. **Genuinely partial source map.** The original e has domain
   `SupportCarrier (Vertex F K) s`; we construct the
   membership proof for each local vertex before applying e.
   There is no total map of the old stage or the countable
   birth carrier.
4. **Nonedges matter.** The induced local map assumes the
   original finite map preserves AND reflects adjacency,
   and concludes the same equivalence on every old–old,
   old–fresh and fresh–fresh local pair. An edge-only
   homomorphism would not determine the request code.
5. **Empty support.** For an empty old support the old case
   has no inhabitants; the fresh case is still covered.
   No arbitrary target vertex is picked, including for
   the target initial stage U₀.
6. **Remaining uniqueness work.** The theorem discharges
   the `hInduced` hypothesis of the one-level target-code
   rigidity theorem (#430). Exact coordinate transport
   `hTarget` must still be supplied by pointwise support
   and fresh-ordinal results. It does not itself assert
   equality of target request tags for two arbitrary maps,
   or the full induction. No manuscript GREEN marker
   should be promoted.

The six reviews are internal mathematical checks, not
independent outside referees. Exact-head Lean compilation,
standard-axiom checks and placeholder scans are mandatory.

```sh
lake build BigHrushovski.CFArbitraryFiniteLocalInduced
lake env lean CheckAxiomsCFTrackBArbitraryLocalInduced.lean
python3 scripts/check_no_placeholders.py
```
