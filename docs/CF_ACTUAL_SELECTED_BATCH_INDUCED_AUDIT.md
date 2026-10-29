# Adversarial audit: actual simultaneous C_F inducedness

29 October 2026

## Claim

The map of all selected old vertices and all selected blocks at one
prescribed target level is induced, not merely edge-preserving.
The hypothesis on the old source is the ordinary induced adjacency
of f on S. Old-fresh and internal fresh-fresh comparisons are no
longer external assumptions: they are derived from the actual
transported StageRequest, whose ordered local graph is the literal
named-base pullback of the source local graph.

The graph of a tagged level contains no edge between different
fresh request blocks. Since the actual target request map is
injective, this no-cross statement reflects every such nonedge.
The result makes no chronological one-block choices.

## Four hostile proof roles

1. **Exact boundary.** For an old u in S and a fresh vertex i
   of request r, the source old-fresh edge exists exactly when
   u is a member of the literal support P_r and its local code
   records the edge. In the target, the equivalent statement
   uses the actual support image f[P_r] and the transported
   local graph. The reverse implication requires injectivity
   of f on S; otherwise a different old vertex could share
   the target image of a support vertex.

2. **Internal graph.** The named-base pullback changes only
   the names of the old support; the fresh Fin ordinal is fixed.
   Thus every fresh-fresh edge and nonedge agrees. The
   complete local adjacency matrix was previously verified
   independently. No hypothesis of positive-edge
   homomorphism alone is substituted for inducedness.

3. **Cross-block separation.** A source pair from two
   distinct requests is a nonedge in the actual source tagged
   level. The target tags remain distinct by complete-code
   injectivity, so the corresponding target pair is also a
   nonedge. The graph check covers *both directions*.

4. **Finite lift scope.** This proves inducedness of the
   actual selected batch map under the induced old-source
   hypothesis and d-closedness of each transported support.
   The full map is separately injective and has a
   d-closed image. Canonical stage-order preservation,
   b-value compatibility and induction through represented
   levels remain to be verified. The finite unique
   level-lifting and countable monoid statements are
   not certified.

## Lean verification

Three exact axiom endpoints are registered in CheckAxioms.lean.
Full Lean compilation, the standard-axiom and placeholder audits
and all finite regressions must pass on the same revision
before the manuscript gains a green marker for inducedness.
No sorry, admit or new axiom is permitted.

These are role-separated adversarial mathematical reviews
within the project, not claims of independent human referees.
