# Track D: Ramsey-transfer validation (1 November 2026)

**Pinned inputs.** Lean main `1f5fcd06fe6fcdbfdfeab997125b31609df98b38`; paper main `264bc23505f2c6c9fda83b544edf55badcd120b2` (v52). This branch has its own `BigHrushovski/RamseyTransfer.lean`, `BigHrushovski/CFLevelRamseyTransfer.lean`, `TrackDCheckAxioms.lean`, and dedicated workflow. It does not edit the shared umbrella, global axiom list, or manuscript markers.

## Precise certification boundary

The embedding version of `DegreeAtMost E S action d` means: for each finite number of colours and every colouring of embeddings of the chosen finite structure, there is a self-embedding whose postcomposition image uses at most `d` colours. The finite palette makes this formulation valid also when the finite pattern is empty.

* `degreeAtMost_iff`: given two bijections (finite embedding spaces and self-embedding spaces) **and** equivariance under postcomposition, the complete sets of Ramsey upper bounds coincide.
* `exactDegree_iff`: the least bounds coincide, so the proof does not transfer only the upper bound and silently assume unavoidability.
* `levelDegree_iff` / `exactLevelDegree_iff`: specialize to increasing tuples `Fin m ↪o L` and increasing self-maps `L ↪o L`. The level-lift equivalences and compatibility are explicit hypotheses, **not conclusions**.
* `degreeAtMost_of_coordinateHost`: for the C0 coordinate-host argument, an encoding, a return map, and a compatible construction of actual self-embeddings suffice. This requires no false claim that the host is globally order-isomorphic to C0.
* `finiteRamsey_of_levelCodes`: an actual finite combinatorial arrow on level tuples gives the corresponding finite arrow for the concrete structures when the host embeddings have unique codes and composition preserves them. The represented A-within-B coordinate tuples need only be mapped into all a-subsets of b; surjectivity there is unnecessary.\n* `singleton_degree_one` / `two_unseparated_lifts_not_degree_one`: formal negative control. One coordinate type has degree one; two embeddings lying above it, with no self-map that can separate their colours, do not. Hence a surjective level code alone is insufficient.

The workflow builds the otherwise unimported Track D file, checks nine exact `#print axioms` endpoints against the whitelist of ordinary logical axioms, and runs the repository's placeholder scanner. The standard project build does not imply that a new file, absent from the umbrella, was checked.

## Manuscript-to-formalization ledger

| Paper statement | Exact missing mathematical identification | Status |
| --- | --- | --- |
| `lem:C0-coordinate-host`, §4 | Construct W with **complete** C and J values; prove that embedding a finite ordered closure into W is uniquely fixed by an increasing coordinate tuple; construct the graph-functional return map and prove it is order-preserving on the relevant finite closed ordered substructures. Prove that every `ψ T_h φ` is an ordered self-embedding. Then instantiate the coordinate-host transfer and the ordinary infinite Ramsey theorem. | Abstract transfer isolated; concrete coding/open |
| `thm:big`, §4 | Degree-one portion above; independently show recurrence inside *every* unexpanded functional self-copy before claiming equality with the number of realized induced orders. These orders need not have the expansion property. | Open |
| `thm:CF-D-BRD1`, §4 | Obtain the bijection `Emb(A, Mhat_F) ≃ (Fin m ↪o ℕ)` from existence **and uniqueness** of the prescribed level lift, including genuinely partial old sources. Show each increasing map of ω lifts and commutes with finite maps. Apply the ordinary infinite Ramsey theorem. | Exact abstract transfer isolated; blocked by Track B |
| `thm:UF-rational-reduction` (ii),(iii), §5 | Establish `Emb(A,U_F) ≃ (Fin m ↪o ℚ)` and the full self-embedding correspondence, including finite substructure coverage, compatibility, and monoid multiplication. Apply the transfer lemma; import/verify Devlin's theorem to obtain D_m. Level-order density and end-freeness are separate. | Conditional abstract exact-degree transfer; concrete equivalences/open |
| `thm:CF-D-Ramsey`, §10 | Use the **finite** Ramsey theorem on level subsets, closure under finite unions of represented substructures, and the finite unique lifts. The combinatorial transfer itself is now isolated in `finiteRamsey_of_levelCodes`, but closure and unique lifts are still needed. | Conditional finite transfer isolated; concrete instance/open |
| `cor:UF-big-ramsey-structure`, §5 | Beyond exact degrees, prove that all Devlin types are realized on *every* rational copy and one expansion-preserving self-map occurs inside any copy (recurrence). The finite and ω-recursive Devlin-pattern extension construction remains a separate obligation. | Open |
| Three concrete Ellentuck spaces, §6 | The abstract Ellentuck theorem does not discharge the concrete A.1–A.4 approximation and topological closedness assumptions. Owned by Track E. | Not certified in Track D |

The full tuple equivalence is **not** a conclusion of bijectivity of the level map, and a bound for the concrete ω-level presentation does **not** imply the Devlin degrees of its rational homogeneous limit. In particular the two level orders are not interchangeable.

## Internal adversarial referees (role-separated checks, not external referees)

**Embedding referee.** Checked the quantification over arbitrary finite colourings and self-embeddings in `DegreeAtMost`. A finite palette avoids implicit nonemptiness of the embedding space; the action must be verified as genuine postcomposition in an application.

**Uniqueness referee.** Checked failure of the reduction when a coordinate has two embeddings: the Bool-to-Unit collapse with the identity action is a concrete counterexample. The theorem accordingly requires a bijection, not just an injection or surjection.

**C0 host referee.** The coordinate host W only carries a partial comparison by coordinates, so it cannot be treated as an ordered copy of O0*. The return map must be known to preserve order on each relevant finite closed ordered image. The separate host theorem makes precisely this compatibility visible.

**CF partial-source referee.** The old source represented at a step may be a proper subset of the entire old stage (including the empty-target case). Earlier total-old-stage map theorems cannot discharge the required unique partial-source level lift. No downstream green marker is justified by the transfer lemma alone.

**Rational-level referee.** Finite lift compatibility, existence/uniqueness of the infinite lift, and closure under composition are needed before speaking of a monoid isomorphism. The equality with tangent numbers additionally needs the classical Devlin result and the lower-bound unavoidability.

**Formalization referee.** The dedicated source is intentionally unimported by the shared umbrella pending integration. Only a successful Track D workflow run certifies the nine declarations here. A green marker needs separate source-to-manuscript comparison and an integration audit.

## Next obligations within Track D

1. Establish the concrete finite Ramsey instance by giving canonical A/B copies in a finite closed host, the level-code bijections, and their compatibility; the finite transfer lemma is now isolated.
2. Formalize the concrete coordinate model for one-generated C0 closures, including complete J and C values and reflection of nonedges.
3. After Track B's actual partial-source lift is certified, instantiate the ω-level transfer; after countable rational finite lifting is certified, instantiate the exact Devlin reduction.
4. Add the concrete instances to the global axiom ledger **only in an integration PR**; do not turn paper markers green for these abstract statements alone.

No standalone manuscript PDF is claimed by this code-only PR. No external panel, full paper verification, or fresh Lean build is claimed until the referenced CI jobs have actually succeeded.

## Continued C0 coordinate-host verification (1 November 2026)

Concrete modules added after the initial conditional Ramsey transfer:

- `C0CoordinateHostGraph.lean`: countable C0 edge coverage, graph recovery from J(v)=N(v) intersect C(v), equivalence of complete (C,J) and (E,C) embeddings, and no crossing edges between exclusive parts of two C-closed sets. The new two-closed-sets endpoint was renamed `genericC0UnaryClosed_noCross_between` to avoid colliding with the existing stage-specific theorem in `C0UnaryClosedStrong.lean`.
- `C0CoordinateClosedRestriction.lean`: complete C/J images on finite closed subtypes, nested values, and equality after repeated restrictions. A nonclosed domain can lose unary values: C(0)={0,1}, C(1)={1}, restricted to {0}. Closedness is essential.
- `C0CoordinateNormalForm.lean` and `C0CoordinateLiteralCode.lean`: literal coordinate support e[D], distinguished coordinate e(a), complete ordered adjacency-pair matrix and unary-incidence matrix. The code-rigidity endpoints recover all edges, nonedges, and complete unary-value membership on the SAME source carrier with the SAME increasing coordinate map. Equivalence for arbitrary different pointed source presentations and construction of W are not yet proved.

### Internal adversarial panel (role-separated, not external referees)

1. Graph/nonedge reviewer: an embedding requires the biconditional adjacency matrix, not only positive edge preservation.
2. Complete-function reviewer: every unary value member is recorded. Component indices, degrees or old-neighbour counts would discard essential data.
3. Empty case reviewer: each pointed code has a root in its support. The empty finite Ramsey pattern must be handled separately.
4. Representative reviewer: the finite normal form does NOT yet certify the entire quotient of pointed triples, or restriction of one generated code to another. A cross-source pointed isomorphism theorem is still required.
5. Countable reviewer: construction of the return map psi: W -> O0 needs actual ordered functional tail extensions, still dependent on Track A.
6. Certification reviewer: only exact-head dedicated Track D CI can establish kernel compilation and standard axiom usage. The first dedicated CI uncovered a theorem-name collision and the next an invalid field-notation token; both are corrected, but the latest new endpoints remain CI-pending.

### Finite adversarial regression

`scripts/check_c0_coordinate_host_finite.py` exhausts 156 compatible extensive/transitive set-valued closures and edge-covered simple graphs on 0, 1, 2 or 3 vertices, with counts 1, 1, 7, 147. The 155 figure excludes the empty structure. It checks graph recovery, no-cross finite closed cuts, full C/J value preservation in closed restrictions, two-stage restrictions, exact literal matrix fidelity for multiple increasing coordinate assignments, and counterexamples when edge coverage or closedness is omitted. This is a finite test, not a proof of the infinite host theorem.

### Next mathematical target

Prove the **finite pointed subcode theorem**: restriction to the closure generated by a point produces a permitted literal pointed diagram, and successive restrictions agree exactly as pointed codes. Then assemble W from these permitted codes, prove a unique increasing coordinate realization for every finite ordered closed pattern, and construct an order-compatible return map using the functional tail-extension theorem. No manuscript green markers should be added before these concrete results and their exact Lean audits.
