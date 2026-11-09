# Track F — finite sink-star construction, adversarial audit (8 Nov 2026)

Dependent on orientation integration PR #270. Manuscript v52,
Section 7.4.5: the proof that the sink graph of N_F has the Rado
extension property adjoins one sink z and, for each selected old
sink a, one new predecessor x_a with exactly the arrows x_a→a,z.

This branch constructs **that genuine finite two-orientation**
using a tagged old/new carrier. It proves arrow preservation and
reflection on the old part; the new sink and arm outgoing values;
absence of loops, opposite arrows and outdegree violations;
and that the old part is successor-closed, hence strong for the
ordinary 2|X|-|E(X)| predimension.

**Not yet established in Lean:** the exact relative predimension
identity δ(W)=δ(D)+2ε+2t−εt−s; the piecewise threshold growth
q, membership in the finite F age, and **strict** F d-closedness
of the old base. These are the essential subsequent inputs to the
strong finite extension property and Rado sink-graph lemma.
The independent regression checks the arithmetic identity and
strict relative inequality on all small subsets, without promoting
either to a Lean theorem.

## Six adversarial referee roles

1. **Tagged-domain referee:** every selected old sink indexes one
   distinct arm, and new sink is distinguished from all old vertices;
   empty U is allowed.
2. **Direction referee:** arrows have tails at arms and targets at
   their selected old sink and new z; old outgoing values are untouched.
3. **No-label referee:** outgoing sets are unordered complete values;
   no arbitrary first/second successor labels are inserted.
4. **Predimension referee:** old-base successor-closedness yields
   weak strongness only; it must not be promoted to F strict d-closure.
5. **Growth referee:** the proof of DF membership requires q(n+1) ≤
   q(n)+1 and q(2n+1) ≤ q(n)+2 with the correct small cases.
6. **Infinite referee:** no Rado graph, absolute sink relation,
   unavoidability, or infinite big Ramsey lower-bound theorem is
   claimed. The exact-head Lean build, axioms, placeholders, and
   independent finite regression are explicit acceptance gates.

Adversarial negative case: the fork x→a,b has the two sinks {a,b}
successor-closed but δ({a,b}) = δ({a,b,x}) = 4. Thus the
distinction between strongness and strict d-closure is essential.
