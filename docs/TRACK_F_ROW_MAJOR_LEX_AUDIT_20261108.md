# Track F — literal row-major lexicographic code (8 November 2026)

Stacked on the concrete fixed-old-part PR #383, itself dependent on
#377 and Track F integration PR #270. No paper text or validation
markers are modified.

The manuscript chooses the lexicographically least directed adjacency
matrix after fixing the earlier order of the lower successor part.
The finite ordinal index in PR #383 was an arbitrary complete-code
order, so it did not formalize **lexicographic** minimality.

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

1. **Lex referee:** the outer order must compare rows in index order,
   not use the incidental \`Fintype.equivFin\` numbering.
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
