# Adversarial audit: candidate countable C_F graph

16 October 2026

## Actual definition

The vertex type is the countable dependent sum of fresh
request-tagged layers. Define x~y when there exist a finite stage n
and two representatives a,b in that stage with birth(a)=x,
birth(b)=y, and a adjacent to b inside its finite-stage graph.

The definition uses no graph relation postulated on the limit.
Symmetry is inherited from the witness stage. Irreflexivity
uses injectivity of the stage-to-birth map: two representatives
of the same birth vertex in the same stage must be equal.

## Four separate adversarial mathematical checks

1. **Loop referee.** Irreflexivity is not automatic from finite
   graphs unless distinct finite representatives cannot be
   identified in the birth carrier. The proof explicitly invokes
   toVertex_injective before using stage.graph.irrefl.

2. **Witness-stage referee.** The existential definition does
   not require choosing a least stage, a global vertex order,
   or an equivalence class of representations. Forward
   preservation of each finite stage edge is immediate.
   Reflection of nonedges is a separate missing theorem:
   it requires all later embeddings to preserve and reflect
   adjacency and comparison of representatives in a common
   finite later stage.

3. **Cofinality referee.** Every single birth vertex has a
   representative at its successor birth stage. To apply
   predimension to arbitrary finite sets in the countable
   graph, one must additionally show all members of each
   finite set admit representatives in *one* later stage,
   not merely separate stages.

4. **Genericity referee.** The graph definition does not
   imply C_F membership, global strict d-closedness of stages,
   or the finite-extension property. The finite-stage
   growth-class theorem is conditional on restricted d-closed
   free amalgamation; completeness of each local catalogue
   is conditional on a uniform one-generator closure bound.
   Those exact assumptions must be transported into the
   countable construction before identification with M_F.

In particular the limit must not be annotated GREEN in the
manuscript merely because the GraphOn object typechecks.

These are separated internal adversarial proof obligations,
not external independently spawned referee agents.
