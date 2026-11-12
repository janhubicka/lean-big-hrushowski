# Track B: one-level target request rigidity — 12 November 2026

Stacked on the complete local graph reading theorem in PR #424.
The final finite uniqueness induction will compare two maps
that agree on the earlier source. This module isolates the
remaining one-block code calculation from that induction.

## Exact statement

A source request r at level n has a literal local carrier:
its named old support together with the entire fresh Fin block.
Suppose a (possibly partial) map e is induced on that complete
local carrier and carries old and fresh coordinates to the
actual target request t at level m by two **order isomorphisms**.
Then the complete ordered adjacency code of r equals that of t,
including all nonedges.

If two target requests t1 and t2 at the same target level have
the same **literal support** and fresh size and each arises by
such a partial induced coordinate map from r, then t1=t2 as
literal StageRequest records. Their ordered matrices are not
assumed equal; they are derived from inducedness and the
ordered coordinate transports.

## Six adversarial referee roles

**Referee A — no global extension.** e is defined on the actual
local carrier, not on a complete source stage or the countable
birth universe. The inducedness premise involves exactly
pairs in that local carrier.

**Referee B — complete graph, not only edges.** The local
code bridge uses `birthRequest_localAdj_iff`, an equivalence,
and `hInduced` is an equivalence. Consequently both edges
and nonedges are compared; old–old, old–fresh and fresh–fresh
pairs are covered.

**Referee C — ordered coordinate maps.** The old-support map
and the fresh-ordinal map are `OrderIso`, not arbitrary
bijections. The complete adjacency matrix enumerates old
coordinates in increasing order, then fresh ordinals; an
unordered permutation would not preserve its bit order.

**Referee D — distinct supports remain distinct.** Even
isomorphic old supports do not give equal request tags.
The final uniqueness endpoint separately assumes
`t1.support = t2.support` as literal finite sets; this
must later be proved from exact complete b-values and
agreement on earlier source vertices.

**Referee E — no invented same-level map.** Both target requests
are explicitly at the SAME level m, and their request types
are defined over `stage F K m`. In the final application
the prescribed target-level assignment must supply this
hypothesis. This theorem does not merge requests at
different levels.

**Referee F — remaining bridge and dependency.** The theorem
does not construct order isomorphisms or the coordinate
commuting equations from arbitrary RH embeddings. Those
come from the partial support/block image lemma, ordinal
rigidity and canonical order coherence, followed by
agreement on the earlier cut. The remaining represented-level
induction is unproved. It must not be promoted to a green
uniqueness marker. The stacked PR depends on #424 and
must pass exact-head Lean and standard-axiom audits.

## Mechanical verification

```sh
lake build BigHrushovski.CFOneLevelTargetTagRigidity
lake env lean CheckAxiomsCFTrackBOneLevelTagRigidity.lean
python3 scripts/check_no_placeholders.py
```

This document records internal six-role adversarial reasoning,
not independent outside human refereeing.
