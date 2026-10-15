# Adversarial audit — explicit finite tagged simultaneous C_F graph
15 October 2026

The candidate CFStageCatalogue.levelGraph constructs a graph on

    U ⊕ (Σ r : StageRequest U, Fin (newSize r)).

It contains **every** actual old vertex once, and gives each finite
catalogue request its **own disjoint fresh block**. The graph relation
is the union of the old adjacency relation and the complete adjacency
relations of the local codes transported along their tagged inclusions.
It introduces no other edges.

This is a genuine graph construction, rather than an existential
assumption that a family of blocks can be attached.

## Four adversarial mathematical referees

**1. Distinct-request referee.** Two requests with isomorphic local
codes, or even identical supports, are different requests when their
full records differ. Fresh vertices therefore carry the *request*
itself as a tag; relying only on local vertex indices would identify
unrelated fresh blocks. The proof levelGraph_no_cross_fresh shows
that fresh vertices of different request tags cannot be adjacent,
without needing an unproved independence assumption.

**2. Common-base referee.** Different local codes can share old
vertices, and their induced old adjacencies must not conflict.
Each stage request's OrderedLocalType.base_agrees identifies its old
graph with the corresponding *induced graph on its actual support*.
The global graph includes the old adjacency relation literally.
A follow-up theorem must prove it induces the old graph exactly,
not merely that all its old edges are present.

**3. Whole-block referee.** The complete graph of a local code,
including edges between two fresh vertices of the **same block**,
is retained by its local tagged inclusion. Recording only the
old-to-new boundary edges would change predimension and could
destroy minimal strict d-closedness. The stage graph is defined
from complete local adjacencies, not from support masks.
A follow-up induced-subgraph theorem is still required.

**4. Strict closure and class referee.** The fact that the graph
is a tagged no-cross union does not by itself show that the entire
old stage is d-closed in the resulting simultaneous amalgam. That
requires strict closure for intermediate sets spanning several new
blocks, and proof that the appropriate local supports stay d-closed
as more blocks are added. Even after that graph-theoretic step,
membership of the resulting graph in the **particular class C_F**
requires the published free-amalgamation hypothesis and its
growth-function restrictions. No countable genericity or
block-root theorem follows from the raw graph construction.

## Independent finite diagnostic

scripts/check_cf_tagged_simultaneous.py computes the actual finite
catalogue over all old graphs with at most three vertices (using
2-sparsity only as a sample admissibility predicate), then constructs
the graph on old vertices plus disjoint request-tagged fresh copies.
It compares the *complete* local adjacency for every code, checks
literal preservation of the old graph, ensures no fresh vertex meets
an old vertex outside its support, and rejects all edges between
distinct fresh block tags.

These bounded tests are diagnostic. The Lean endpoints require the
standard-axiom audit and placeholder scan before any green marker.
The next proof will establish *induced* equality on all old and local
pieces, followed by finite strict d-closedness and exact support
preservation for all requests simultaneously.
