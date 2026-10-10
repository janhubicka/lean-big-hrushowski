# Reusable Ramsey libraries for The Big Hrushovski

This note records existing, independently developed Lean theorem endpoints.
No Ramsey, Milliken, or Ellentuck consequence is claimed to be verified in
the Hrushovski manuscript merely because these theorems are available.

## Installed source repositories and usable endpoints

* [`lean-successors`](https://github.com/janhubicka/lean-successors):
  the successor-tree / Hales--Jewett machinery on which the current
  Hrushovski repository is already based.
* [`lean-milliken`](https://github.com/janhubicka/lean-milliken),
  [`Milliken/MillikenTheorem.lean`](https://github.com/janhubicka/lean-milliken/blob/main/Milliken/MillikenTheorem.lean):
  `Milliken.Chapter6.milliken` and
  `Milliken.Chapter6.milliken_onBasicNeighborhoods`. These are unconditional
  endpoints for homogeneous strong subtrees over a finite nonempty
  alphabet. The repository constructs A.1--A.4 and metric closedness for
  its **own** strong-subtree approximation system.
* [`lean-ramsey-space-todorcevic`](https://github.com/janhubicka/lean-ramsey-space-todorcevic),
  [`RamseySpace/AbstractEllentuck.lean`](https://github.com/janhubicka/lean-ramsey-space-todorcevic/blob/main/RamseySpace/AbstractEllentuck.lean):
  `RamseySpace.abstractEllentuck_textbook` for a published-axiom
  `AbstractRamseySpace` whose approximation-code image is Tychonoff
  closed; `RamseySpace.abstractEllentuck` for the equivalent metric
  closedness interface. Also
  `RamseySpace.TwoSorted.abstractRamsey` for the two-sorted A.1--A.6
  framework.

## Mathematical integration points

1. **Finite strong Fraïssé construction (current priority).**
   Neither external Ramsey library replaces the finite graph
   predimension, amalgamation, coherent countable union, and fair
   strong-extension property. Use
   `FiniteCatalogue.exists_finite_strong_response` together with
   `FiniteSpan.extendInitialEquiv` and the old-stage graph transport;
   then prove an unbounded increasing chain and its coherent union.
2. **Closure-component enumeration and big Ramsey upper bound.**
   Once the unary closure presentation and its tree of types are
   formalized, identify the actual finite approximation maps and
   pigeonhole statement; only then import the successor-tree or
   Milliken endpoints that match this space.
3. **Ellentuck theorem.** Do not postulate the conclusion as an
   instance. Build the Hrushovski approximation system and verify
   A.1--A.4 using the **published** `ofPublishedAxioms` interface.
   Verify Tychonoff closedness of the approximation-code image.
   Then invoke `abstractEllentuck_textbook`. In particular a
   Ramsey assertion for strong subtrees alone does not automatically
   make the space of Hrushovski functional self-embeddings topologically
   Ramsey.

## Dependency compatibility

At the time of this note all three repositories use
`leanprover/lean4:v4.35.0-rc3` and Mathlib revision
`5bd58ac291422a21f412ae354c91e7d172255a2c`.

However, `lean-big-hrushowski` pins `lean-successors` at
`ce5ce187ef88e28d84a4a465517b3f9c87a0640a`, while
`lean-milliken` pins it at
`57d35508abd0e55cb2387f88360125d6320e3457`.
Importing `lean-milliken` directly will therefore require a
**tested common dependency pin** rather than simply adding a second
Lake requirement. No pinned dependencies are changed by this note.

## Verification convention

A downstream manuscript statement is marked fully Lean-verified only
after its exact concrete Hrushovski instance compiles at a pinned
commit, has a standard-axiom audit, and passes the placeholder scan.
Abstract library endpoints alone justify only an interface marker.
