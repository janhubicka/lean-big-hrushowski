# Adversarial audit: bounded local code over the actual named support

16 October 2026

The new theorem bounded_named_growthLocalType combines the two
previously separated finite interfaces:

* an old-support equivalence P ≃ Q, induced on the old graph,
  relabels a local graph on P⊕B as one on the literal Q⊕B;
* the unique increasing enumeration of B preserves the complete
  graph and C_F membership, and normalizes it to Q⊕Fin(|B|).

The original source graph is assumed to have minimal strict
d-closed extension P<_d P⊕B, exact old-neighbour support, and
growth-class membership. The equivalence transfers these three
properties to Q⊕B. The supplied whole-extension bound
|P|+|B|≤K remains valid because an equivalence preserves
the cardinality of P. The normalized graph therefore occurs in
the bounded ordered type catalogue over *the actual Q*, with
fresh size exactly |B|.

## Separate adversarial proof obligations

1. **No false source replacement.** Q is the designated named
   support, not another abstract isomorphic copy. The old map
   must be induced and bijective on P; a homomorphism, or an
   injection with image smaller than Q, would not justify this
   statement.

2. **Nonedges.** Both stages of normalization use graph
   equivalences and not positive-edge homomorphisms. This is
   essential for all induced subgraph growth inequalities and
   for reconstructing the full local extension.

3. **Strict minimality.** The source hypothesis is minimal
   *strictly d-closed*, not just weakly strong. The transport
   calls the exact IsMinimalDClosedStep theorem and also carries
   the canonical old-neighbour hull. A bare minimality
   assertion without exact support could index a wrong request.

4. **Size bound.** The input is the whole-extension estimate
   |P|+|B|≤K. No such bound follows merely from naming the old
   support. The published Theorem 4.14 of the sparse-graphs
   paper supplies the appropriate K for C_F; instantiating that
   analytic estimate in Lean is a separate remaining step.

5. **Final countable bridge.** The theorem proves existence
   of a named bounded catalogue *code*. It does not itself
   construct the equivalence from an arbitrary finite embedding
   A→M_F, nor assert that the chosen code's entire block is
   embedded over the prescribed source. Those steps must use
   the already certified source-pullback theorem, the finite
   canonical local-support lemma and the global named-code
   response; they are not silently assumed here.

All roles are deliberately separated internal mathematical
adversarial reviews, not external independent referees.
Green manuscript validation is allowed only after this theorem
passes integrated CI with standard-axiom and placeholder audits.
