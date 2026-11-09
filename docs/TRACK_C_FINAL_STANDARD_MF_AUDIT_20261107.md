# Track C — final theorem as stated in the manuscript

This is the end-to-end *mathematical* identification of the
canonical C_F birth construction with the published countable
strong Fraïssé limit, under the exact standing assumptions
and the **ordinary** finite strong extension characterization.

It depends on:
- the singleton-request and birth-carrier infinitude proofs
  (#315 and #357, merged);
- the published growth and strict genericity proofs (#277,
  #269, #302, #312, #360 and #362);
- the native Fraïssé-limit interface (#365); and
- the conversion of the usual arbitrary-finite strong extension
  property to the literal Nat-interval API (#367).

## Logical inputs

F is precisely a map from nonnegative reals to nonnegative reals
with F(0)=0, monotonicity and unboundedness. The independent
class properties are free amalgamation over strictly d-closed
substructures, strict d-closedness of the empty set in each
finite C_F-member, and one-vertex membership F(1)≤2.
No extra 'level nonempty', 'inverse K' or 'external Nat carrier'
hypothesis appears.

A comparison structure `M_F : GraphOn V` must have the
*defining* strong Fraïssé-limit properties:
(1) infinite countable enumeration; (2) full finite age C_F;
(3) covering strict d-closed finite chain; and
(4) the ordinary arbitrary-finite strong extension property
which fixes any prescribed induced strong copy of its base.

The structure does not contain or assume an isomorphism to the
birth graph; that is the theorem's conclusion.

## Adversarial referees — independent logical roles

**Hypotheses referee:** the only numerical age inputs are
F(0)=0 and F(1)≤2 for the empty and singleton graphs.
Monotonicity/unboundedness supply the exact canonical K.
The abstract class assumptions are retained, not inferred
from the numerical data.

**Fraïssé referee:** the comparison object has *exactly*
the manuscript's existence/union/age/extension
characterization. The native finite response is **derived**
from the usual arbitrary-finite diagram response
(#367), not added as an unexplained axiom.

**Embedding referee:** the extension map preserves and
reflects all graph adjacency and nonadjacency, fixes the
entire prescribed old map, and produces a globally
strictly d-closed image. No weak-strong substitution or
implicit graph homomorphism is used.

**Carrier referee:** the comparison model lives on an
arbitrary actual vertex type, with an honest countably
infinite enumeration; no quotient, added dummy vertices,
or assumed birth-graph isomorphism enters its data.

**Countability referee:** the canonical birth graph is
infinite because a *literal singleton request* is present
at every stage by the class assumptions; countability
alone was not used to infer infinitude.

**Free-amalgamation referee:** class membership of all
canonical finite stages is checked using the independent
strict free-amalgamation hypothesis. This is not deduced
from monotonicity or F(0)=0.

**Certification referee:** the **whole final theorem** must
pass its own Lean kernel build and exact `#print axioms`,
after upstream modules have compiled. Its implication
cannot be promoted to a manuscript green marker solely
from earlier component CI.

**Editorial referee:** this PR does not alter manuscript TeX.
When CI and clean integration are complete, revise the
pre-existing validation comments and add exactly one
`\leanverified` marker to the full C_F finite-level
lemma, subject to a final adversarial comparison of
the printed statement and the Lean theorem.

At submission this is a proposed full proof with CI pending.
The referee roles are internal adversarial checks, not an
external human peer-review panel.
