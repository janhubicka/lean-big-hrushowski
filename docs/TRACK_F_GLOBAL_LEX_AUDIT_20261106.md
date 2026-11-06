# Track F - finite lexicographic order construction (6 November 2026)

This is an independent finite construction. Given a legal
component ranking of the actual SCC dependency order, and
local natural-number ranks injective within each SCC, order
the labelled vertices lexicographically by their component
and local rank. The numerical key is injective, so the
relation is irreflexive, transitive and total on distinct
vertices. It places proper successors before their
sources and cannot interleave two SCCs.

The result supplies the *existence of a successor-first,
component-interval strict order* for every legal component
ranking. It does not assert the local ranks obey the
manuscript's canonical complete adjacency-code rule.
The crucial remaining task is choosing the correct canonical
local order over each already ordered lower part, and proving
a bijection with all permitted ordered expansions.

Internal adversarial checks:
1. Distinguish the component rank from the local rank;
   local numbers may repeat in distinct SCCs.
2. Check the key is injective on each SCC; a constant
   local rank on a directed triangle violates totality.
3. Check every proper successor precedes its source;
   reversing the ranks of a single directed edge fails.
4. Check each SCC is an interval even with directed cycles.
5. Empty orientation and empty component ranking are included.
6. Verify new Lean endpoints with isolated build and
   standard-axiom audit; independent Python tests do
   not substitute for kernel certification.

Exhaustive regression: 653 orientations on up to four
labelled vertices, 1,586 legal component rankings and
3,172 constructed orders under two locally injective
choices. No infinite big Ramsey theorem is asserted.
