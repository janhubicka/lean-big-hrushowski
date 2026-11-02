# Track F — finite component closure and linear-extension data (2 November 2026)

Base: \`janhubicka/lean-big-hrushowski\`, Track F integration commit
\`76759e311f0cf8e69b699f2538f41afd41539c6d\`.

## Exact new statements

* \`N0ComponentLowerPart.lean\` defines the actual complete
  successor closure \`C_B\` of a strongly connected component and
  \`P_B=C_B\\B\`. It proves \`C_B=scl(x)\` for each generator \`x∈B\`,
  that \`P_B\` is successor-closed and strong in \`C_B\`, and that
  both sets depend only on the component and not the vertex.
* \`N0ComponentLinearExtensions.lean\` gives a literal finite type
  of actual SCCs, bijective component ranks taking consecutive
  finite-ordinal values, and the subset of such rankings that
  respects proper successor dependency. The count \`ell(A)\` is
  the number of these legal rankings. Every corresponding prefix
  is successor-closed and strong.
* An abstract finite data-count lemma combines each legal
  component rank with independent local finite choice sets,
  giving \`ell(A) * product_B |choices(B)|\`. This is a theorem
  about **data**. There is not yet a proved bijection between
  those data and all permitted vertex linear orders, and the
  actual stabilizers live in the induced orientations of \`C_B\`,
  rather than in the full ambient permutation group.

## Internal adversarial reviewers

1. **Closure reviewer:** verified \`P_B\` is closed because a path
   back into B would make its source strongly connected with B.
   This does not require acyclicity of the orientation.
2. **Component identity reviewer:** component closures and lower
   parts are invariant under replacing the generator within B.
3. **Rank reviewer:** rankings are bijections of the *actual*
   SCC type onto a finite ordinal, and proper successors
   precede the component; rankings of arbitrary vertices are not
   substituted for component orders.
4. **Counting reviewer:** a product of independent local option
   sets is not yet the number of permitted vertex orders.
   Dependency of a local representative on the previously
   ordered lower part remains to be handled.
5. **Certification reviewer:** isolated CI, axiom and placeholder
   checks are required before any new statement is labelled
   machine-verified. No manuscript prose or markers change.

Independent exhaustive regression: all 30,887 orientations on up
to five vertices, 153,742 closed lower-part configurations,
348,658 same-component comparisons, 94,694 legal component rankings
and 512,869 closed rank prefixes. This is finite evidence, not an
infinite Ramsey theorem.

Next: construct induced finite orientations on \`C_B\`, define the
true pointwise stabilizers \`Aut(C_B)_(P_B)\`, and then assemble the
bijection with permitted vertex orders. The degree-one Ramsey
theorem and recurrence remain independent infinite obligations.

## Exhaustive local canonical-code fibre audit

The new independent script `check_track_f_n0_local_fibres.py` examines all 30,887 admissible finite orientations on at most five vertices. For each of the 106,264 distinct component closures in those labelled graphs, and for every permutation of its lower part, it compares the lexicographically minimal complete directed adjacency matrix over all internal component orders with the pointwise stabilizer cardinality. In total there are 478,199 ordered lower-part configurations and 1,170,649 tested local internal enumerations. Every fibre has size exactly `|Aut(C_B)_(P_B)|`. This detects accidental setwise stabilizers, incomplete adjacency codes, and dependence of the fibre size on the prior lower-part order. This is finite evidence only; the general equivalence with all global permitted vertex orders remains a Lean proof obligation.
