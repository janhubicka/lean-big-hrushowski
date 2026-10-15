# Adversarial referee audit: the finite one-level C_F response

16 October 2026

## Mathematical statement

Fix a finite old graph U, an actual strict d-closed old source
A <=d U, a literal support P <=d U with P subset A, an
admissible complete ordered minimal local type t over P,
and a certified cardinality bound n <= K(P).
The actual simultaneous tagged level contains a specific request
r=(P,t). Its fresh block B_r satisfies

    A union B_r <=d U_next,

and its local support+block graph is an induced copy of the entire
code t, including **nonedges**. The witnesses are literal request
tags, not postulated abstract embeddings.

The theorem does not yet assert preservation of the global
lexicographic order. The ordering of fresh tags must be handled
when proving the finite level-embedding monoid.

## Four separately hostile mathematical referee passes

1. **Literal support / naming.** The code is constructed over the
   subtype of the actual P subset U, not over an unrelated isomorphic
   base. This matters: the graph might have several isomorphic supports,
   and the correct request must attach to the chosen copy of P.
   requestOfOrderedLocal constructs the exact stage-tag.

2. **Full inducedness.** A graph homomorphism into the tagged batch
   would not suffice: the prescribed minimal local extension may
   contain nonedges within its fresh block or across its support.
   levelGraph_local_adj_iff proves adjacency *equivalence*
   for every two code vertices. localTag_injective supplies
   the injectivity of the complete local representation.

3. **D-closure after unrelated requests.** The chosen fresh block
   cannot merely be closed in U union B_r. Other requests at the
   same level could introduce intermediate subsets. The exact
   chain is A union B_r <=d U union B_r <=d U_next.
   The first inequality requires strict no-cross right-factor
   closure using P subset A; the second is the arbitrary-sub-batch
   theorem of PR #151. PR #152 packages this for arbitrary
   supported families.

4. **Incomplete passage to the limit.** No amount of finite
   closure or code enumeration alone gives a countable generic.
   The remaining construction must align the varying finite
   carriers by coherent induced injections, establish coverage,
   verify one-level response for *every* available literal support
   after transporting a minimal local code, and then invoke
   the already certified finite minimal d-closed decomposition.
   A separate fair enumeration of arbitrary multiblock diagrams
   is mathematically unnecessary if all minimal local requests
   are attached at every level, but this has not been formalized.

## Extra boundary controls

* If P is not contained in A, no-cross over A need not hold,
  and the one-level closure conclusion can fail.
* Merely storing a size bound is insufficient: t must belong
  to the Allowed predicate and match the actual induced graph on P.
* The source A must be strictly d-closed, not just a graph-induced
  subset or weakly self-sufficient substructure.
* Lexicographic order preservation and the functional R,H language
  are **not** consequences of the adjacency theorem.

The exact green marker requires a fully passing integrated Lean
build, standard-axiom audit, placeholder scan, and a final
commit check. Until then these claims are candidate proofs.

The referee roles above are deliberately separated internal
adversarial passes rather than externally instantiated agents.
