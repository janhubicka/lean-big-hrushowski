# Track C — the literal singleton StageRequest

This is the precise finite statement missing from the manuscript's
countable C_F genericity lemma: if the empty support is strictly
d-closed in the old finite stage, the one-vertex no-edge graph
belongs to the growth class and the permitted size bound is at
least one, then the actual `StageRequest` catalogue contains a
one-vertex minimal d-closed extension over the **empty literal
support**, with the exact support-hull condition.

The proof does not use a total old map, any fake target vertex or
a countable genericity premise. The old component of the local
carrier is empty, and the fresh component consists of `Fin 1`.

## Internal adverse referee panel

- **Minimality referee:** the local extension is proper and the
  one-vertex carrier has no nontrivial intermediate substructure.
  Both δ(∅)=0 and δ({v})=2 are checked.
- **Class referee:** growth membership is checked on both possible
  finite vertex sets; the exact inequalities F(0)≤0 and F(1)≤2
  are explicit. Neither monotonicity nor unboundedness is invoked.
- **Support referee:** the old part is the literal empty subset of
  the old graph. Its d-closed hull is empty and the local code has
  no old neighbours; no support is spuriously enlarged.
- **Bound referee:** one fresh vertex requires 1≤K(0). This is a
  separate input and must next be derived from the published
  exact inverse bound and singleton class membership.
- **Certification referee:** no manuscript lemma marker is changed
  before the isolated source builds and passes the exact axiom
  audit. The remaining class-level and finite-stage hypotheses
  must be discharged, not silently added to the paper.

Negative tests: F(1)>2 excludes singleton membership; K(0)=0
excludes a positive-size request; a non-d-closed empty support
would not define a StageRequest.

At creation this is a proposed proof awaiting Lean CI. This
is internal, role-separated checking, not external refereeing.
