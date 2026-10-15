# Adversarial audit: finite C_F stage-request catalogue

15 October 2026. The object under review is a *finite list of
requests at one old stage*, not a new graph or countable limit.

For a finite old graph U, let P range through its actual vertex
sets satisfying P≤d U. For each such P, the bounded ordered local
catalogue (certified previously) supplies a finite collection of
graph codes over its literally named support. The new StageRequest
combines the precise P with one such complete local code.

## Referee 1 — actual supports rather than abstract types

Two isomorphic d-closed subgraphs P0 and P1 of the same old stage
are distinct extension sites. If U contains two isolated vertices
a and b, both {a} and {b} are d-closed. The local extension
attaching one new neighbour to a has the same graph code as that
over b, but the two requests must both occur. Hence P must be a
literal Finset U and its normalized old carrier a subtype of U;
classifying old supports only by isomorphism would miss requests.

## Referee 2 — finiteness with a support-dependent bound

There are finitely many actual P⊆U because U is finite.
For every P, the caller supplies a finite bound K(P) on the
new-block size. The earlier catalogue module gives finitely
many ordered local graph codes of size n≤K(P), including the
full graph on P⊕Fin n. Therefore the disjoint union of these
finite fibres over all P is finite, even if K varies with P.

Having only finitely many graph codes *at each n* without a
bound on n is not sufficient. The abstract StageRequest
requires the bound explicitly; only the published growth
function supplies its intended concrete value.

## Referee 3 — membership, minimality and exact support

A request is accepted only when its support is d-closed in
the actual old graph. The local code must agree with the
induced graph on P, satisfy its independent Allowed predicate,
be a minimal d-closed extension and recover P exactly from
the old-neighbour hull. It is a complete graph code, not
merely a boundary-neighbour list.

For the bounded Python diagnostic, Allowed is implemented
by simple 2-sparsity. This is *not* a proof that 2-sparsity
defines the growth-function class C_F, nor that the concrete
C_F predicate has already been instantiated in Lean.

## Referee 4 — simultaneous free amalgamation not yet proved

A finite set of requests does not construct U_{n+1}.
To attach all requests one still needs a finite tagged
disjoint union of their fresh blocks and a proof that each
copy has no edge to any other fresh block except through
the old stage. Repeated application of the certified
one-block support-persistence lemma should then keep the
support equal to the intended actual P, but requires
showing P≤d the current prefix at each step. Finally, the
restricted class C_F must be assumed/proved closed under
these permitted free amalgamations.

The finiteness theorem itself does not discharge any
of those graph or countable-structure obligations.

## Independent finite audit

scripts/check_cf_stage_catalogue.py enumerates every old graph
on at most three labelled vertices, every actual d-closed
support P, and all complete bounded local graph codes of
ordered fresh size 1 or 2. It tests exact support, minimal
d-closedness and a sample admissibility predicate, rejects
duplicate request keys and checks that isomorphic but
distinct supports produce different requests.

All three new exported theorem endpoints require successful
integrated Lean build, standard-axiom audit and placeholder
scan. The manuscript should mark only the finite request
catalogue green; the class C_F free-amalgamation and genericity
claims must remain orange until their own concrete proof.
