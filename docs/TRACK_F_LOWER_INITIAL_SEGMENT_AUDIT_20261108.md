# Track F — lower successor parts are initial segments (8 November 2026)

This dependent draft is stacked on #387, #353, and Track F
integration #270. No TeX or validation markers change.

## Mathematical content

For any vertex x of an actual finite two-orientation, the strict
successors of x are *exactly* the vertices of P_B where
B is the strongly connected component of x, C_B is the full
successor closure of B, and P_B=C_B\B. Under any legal linear
extension of the actual SCC dependency relation, every vertex
of P_B occurs strictly before **every** vertex of B in the
lexicographic component-interval order.

Therefore the restriction of that order to C_B has P_B as an
initial segment. The restriction to C_B is essential:
unrelated components outside this closure may precede or follow
P_B arbitrarily. This closes the geometric ordering hypothesis
needed for a canonical local directed-matrix code over the
already ordered lower part.

## Role-separated adversarial audit

1. **Reachability referee:** strict successor is reachability
   excluding mutual reachability; a directed cycle stays inside B.
2. **Lower-closure referee:** C_B is complete successor closure;
   the proof must use all successors, not only immediate arrows.
3. **Precedence referee:** orientation of the SCC dependency
   order has proper successors first, rather than the reverse.
4. **Labelled order referee:** the order is on actual vertices;
   no quotient by graph automorphisms or enumeration objects.
5. **Initial-segment referee:** the initial property is relative
   to C_B, not to all vertices of A; three disconnected sinks
   are a counterexample to the absolute version.
6. **Certification referee:** this is a *finite* ordering lemma.
   It does not identify canonical admissible local-order families,
   establish the global finite bijection/product formula, or prove
   any infinite big Ramsey statement.

Kernel source, exact axiom audit and an independent exhaustive
finite checker are included. Keep draft pending exact-head CI.
