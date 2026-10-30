# Adversarial audit: genuinely partial old-source C_F request transport

30 October 2026

## Logical gap corrected

Finite unique level lifting maps the selected old substructure
S, not necessarily the entire old finite stage U. The existing
transportGrowthStageRequest took a total f:U→V with strict
monotonicity only on S. That is **not equivalent** to a partial
map e:S→V if V is empty and U is nonempty. This occurs in the
first represented level whenever the desired target birth level
is zero, while the source birth level is positive.

The new construction takes e:{u:U // u∈S}→V directly. It
constructs the literal support image of any P⊆S and its
canonical increasing support isomorphism, then constructs
a bounded StageRequest over that image. No global f is
chosen or inferred. Empty source and target old stages
are permitted.

## Five hostile checks

1. **Empty-target referee.** The new statement must not
   assume Nonempty V or extend e to a total U→V. In the
   case S=∅ and V=∅, e is the empty function and each
   support P⊆S is empty. The image support Q is empty,
   so the target request is constructed using a genuine
   order isomorphism between the empty support subtypes.

2. **Named-support referee.** The support image is literal
   CFNamedSupport.supportImage, not an abstract isomorphic
   subset. The order isomorphism is the restriction of
   the exact prescribed e and preserves its values
   pointwise. There is no arbitrary renumbering of old
   vertices.

3. **Graph/predimension referee.** The old graph must be
   induced on P, and Q must be d-closed in the **whole**
   target old graph. These remain explicit hypotheses,
   not consequences of e being increasing. The existing
   named-base relabelling preserves complete growth
   membership, minimal strict d-closedness and exact
   canonical support.

4. **Numerical referee.** The source bound n≤K(|P|)
   transfers exactly because |Q|=|P|. The theorem
   assumes neither monotonicity of K nor extra room
   in the target old stage. The fresh Fin ordinals
   remain fixed.

5. **Lean referee.** Exact endpoints in CheckAxioms.lean
   must be compiled with the full project, standard
   axiom audit, placeholder scan and finite regressions.
   This new construction must not be marked verified
   until the resulting CI on the same commit succeeds.

## Remaining steps

The source and target request codes must be compared
using the partial-support order isomorphism and the
complete adjacency matrix lemma. Then the simultaneous
selected map must be rebuilt with an old-subtype
function instead of a total function. The earlier
full-stage results remain useful conditional lemmas
but do not cover the empty-target case by themselves.

The countable finite unique level-lifting and
embedding-monoid conclusions are not certified.

These are independent adversarial mathematical
perspectives within the project, not externally
commissioned human referee reports.
