# Unary presentation refactor: exact scope and adversarial audit

13 November 2026. Companion to the manuscript referee simplification branch.

Move the existing `finiteSourcePrescribedLift_existsUnique_orderedB`
declaration, with its statement and proof unchanged, to
`CFCompleteFiniteUniqueBLift.lean`. Its direct imports are the arbitrary
finite b-uniqueness theorem and the finite ordered existence theorem.
Remove its former implementation from the combined R/H module, which now
imports the new module and retains the R/H theorem unchanged. Both public
names remain available to old clients. The direct unary entry point no
longer imports the R/H compatibility wrapper.

## Internal adversarial checks

1. The unary statement still has exactly the old hypotheses, including
   full b-closedness, strictness only on represented levels, inducedness,
   complete b-values, order and the reflected level preorder.
2. Both theorem bodies are unchanged, not replaced by new axioms or admits.
3. A new unary-only exact-axiom entry point exercises the smaller interface.
4. The old combined module re-exports the same namespace/name, preserving
   existing imports and check files.
5. No global claim that the transitive import closure contains no R/H
   material is made: this change removes the unnecessary direct wrapper.
6. The R/H compatibility code is not dead: it remains used by the comparison
   theorem and existing clients. Deleting it wholesale would break genuine
   dependencies, despite moving the primary English presentation to b.
7. Kernel compilation and standard-axiom checks must run at the new head
   before this refactor is certified. Textual identity is not a substitute.

These are internal role-separated review checks, not independent human or
spawned model referee reports. No proof deletion beyond the moved declaration
is asserted. No manuscript marker points at this unmerged new module.
