# Track F — literal row-major lexicographic code (8 November 2026)

Stacked on the concrete fixed-old-part PR #383, itself dependent on
#377 and Track F integration PR #270. No paper text or validation
markers are modified.

**Manuscript correspondence (adversarial correction).** Version 52,
Section 7.4.4 ('A fixed system of local orders'), requires choosing
*one ordered representative* for each isomorphism type of a
one-generated closure with its lower part already ordered. It does
**not** stipulate that its chosen representative minimizes a matrix.
Our finite ordinal index in #383 was an arbitrary complete-code order.
The present lex minimum is one concrete uniform way to implement
the manuscript's otherwise arbitrary fixed-representative choice,
not the literal rule printed in version 52.

Here the code type is the nested lexicographically ordered function
space \`Lex (Fin n → Lex (Fin n → Bool))\`. The *inner* order compares
columns left-to-right and the *outer* order compares rows in increasing
index order, giving literal row-major lexicographic comparison. The
equal-code theorem reflects every directed edge and nonedge, not just
the underlying undirected graph. Its code can be substituted directly
in the previously proved fixed-lower minimum fibre theorem: the
minimum lex-class has cardinality
\`|Aut(C)_(P)|\`.

## Six independent adversarial referee roles

1. **Manuscript/lex referee:** version 52 chooses arbitrary uniform
   ordered representatives; lex minimization is a valid *option*,
   not a printed requirement. The outer lex order compares rows in
   index order, not the incidental \`Fintype.equivFin\` numbering.
2. **Orientation referee:** every ordered pair is represented, so a
   reversed arrow or a missing edge changes the matrix.
3. **Stabilizer referee:** the earlier result fixes P *pointwise*,
   with the full automorphism group of the induced closure C.
4. **Old-part referee:** this lemma allows arbitrary fixed positions;
   the actual C_B application still needs P_B to be the first block.
5. **Degenerate referee:** n=0 and an empty lower set remain valid
   through the nonempty family containing the fixed enumeration.
6. **Completeness referee:** the theorem is local and finite; the
   bijection to all globally permitted labelled orders, exact finite
   degree formula, recurrence and infinite big Ramsey assertion
   remain open.

Exact axioms/placeholder auditing is in
\`CheckTrackFRowMajorLexAxioms.lean\`, using the independent exhaustive
row-major Python checker already introduced with PR #383.
This is draft until its own and upstream exact-head CI succeeds.
