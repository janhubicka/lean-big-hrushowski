# Adversarial validation-infrastructure audit (3 November 2026)

Scope: janhubicka/lean-big-hrushowski, independently of any theorem in the paper.

## Concrete defect

The former scripts/check_no_placeholders.py scanned BigHrushovski.lean,
CheckAxioms.lean and files under BigHrushovski/. It omitted the other
top-level Lean check and audit files. At this baseline the repository has
21 top-level Lean files; 19 of these were not scanned by the old script.
The general Lean workflow discovers all CheckAxioms*.lean audit sources,
but compilation and printing their enumerated axioms is not the same as
a whole-source placeholder scan.

The revised scanner inspects all top-level Lean files and all project
modules under BigHrushovski/. Third-party sources under .lake are excluded.
Nested Lean block comments and line comments are ignored without allowing
comment markers inside strings to mask subsequent code. String content is
scanned conservatively. All eight standalone scanner tests must pass in
CI before the scan runs.

## Hostile referee perspectives

1. Coverage referee: list top-level audit sources, including both
   CheckAxiomsCFTrackB.lean and TrackC*Check.lean; ensure none are omitted.
2. Lexer referee: nested comments and line comments are not executable
   proofs; however, an actual sorry, admit, axiom or unsafe in code is caught.
   Literal comment delimiters in strings cannot hide the following code.
3. Dependency referee: check_axioms.py still audits the exact #print axioms
   endpoints. It does not establish that every declaration in every source
   has been printed; the placeholder scan is an independent additional gate.
4. Mathematical referee: passing this scanner, Lake compilation, and the
   standard-axiom check does not establish exact agreement between the
   manuscript hypotheses and the Lean theorem types, nor does it complete
   any countable Ramsey or Ellentuck theorem.

The eight Python regression tests were run locally before opening this PR.
No manuscript validation marker is promoted by this infrastructure change.
These are role-separated internal checks, not independent outside referees.
