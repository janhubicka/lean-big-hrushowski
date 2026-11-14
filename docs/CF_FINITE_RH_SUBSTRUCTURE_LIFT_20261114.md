# Track B: finite lifting on literal R/H-substructures

14 November 2026. Independent Track B endpoint for the shortened
manuscript, Section 3b, Lemma `lem:CF-coordinate-pattern`.

## Identified interface mismatch

The manuscript states the lifting lemma for a finite substructure
of the **actual** expansion with root operation `R` and the
partial hull operation `H`. Previous exact finite uniqueness
(PR #490) and compatibility PRs (#499, #509, #515, #521, #527)
begin instead with a finite `IsBirthBlockClosed` subset,
i.e., closure under the complete auxiliary value `b(v)`.

The previously verified set-level theorem
`birthBlockClosedSet_iff_rhClosed` proves equivalence on arbitrary
subsets. Here we instantiate it to the *literal finite subset*,
then state the unique lifting theorem in the R/H language with
no additional auxiliary b-closure hypothesis.

The new image theorem gives a stronger reusable consequence: an
**arbitrary** injective induced ordered finite R/H embedding has a
literal finite R/H-closed image. It does not assume the map is
the constructed prescribed lift or has a global level assignment.

## Internal adversarial referee panel — six distinct challenges

1. **Closure referee:** A finite graph-induced subset is not
   automatically a functional substructure. Selecting one
   vertex of a nontrivial birth block without its siblings
   or named support can fail b-closure. The new theorem
   explicitly requires R/H closure and proves the b-closure
   consequence via the recovered equation H(R(v)) = C(v).
2. **Partial-operation referee:** `H` is defined only on
   finite sets of roots. Its full domain reflection remains
   in `FiniteSourceRHValues`. Merely preserving values when
   defined would not be the manuscript's embedding notion.
3. **Ordered-language referee:** Both the birth-level
   *preorder* and the actual canonical linear order are
   preserved and reflected. The latter fixes fresh ordinal
   positions within a block; it cannot be omitted.
4. **Finite-label referee:** Strictness is imposed only on
   *represented* source birth levels. A singleton supported
   at source level 1 may have target level 0; no strictly
   increasing map of all omega is claimed or needed. Empty
   source and skipped levels are permitted.
5. **Image-closure referee:** The image theorem first invokes
   the exact finite R/H-to-b-values implication under
   inducedness, injectivity and both orders, then the exact
   full-b-value image closure theorem, and then converts
   back to R/H closure. No assertion that graph embeddings
   alone preserve closure is smuggled in.
6. **Proof-trust/refactoring referee:** The new declarations
   use the existing verified finite lifting and set-level
   closure equivalence. There is no additional axiom, new
   unproved finite existence assumption, global countable
   extension, Ramsey-space assumption, or circular use of
   the manuscript claim. The exact closure and unique-lift
   endpoints have independent `#print axioms` checks and
   full placeholder/Lean CI gates.

These are internal role-separated adversarial checks; they are
not external human referee reports.

## Required verification

```sh
lake build BigHrushovski.CFFiniteRHClosedLevelLifting
lake env lean CheckAxiomsCFTrackBFiniteRHClosed.lean
python3 scripts/check_no_placeholders.py
```

Use the exact PR head. The general Lean workflow runs all
project modules and the finite regression suite.

## Marker and manuscript policy

Do not promote the finite-R/H substructure marker until this
module passes CI. After verification, use the exact endpoint
`finiteRHClosed_existsUnique_levelLift` for the first sentence
of Lemma `lem:CF-coordinate-pattern`, and retain the already
verified finite restriction and composition endpoints, preferably
the actual R/H corollaries rather than merely the auxiliary
b-language modules. Neither these markers nor this PR certify
the later **countable** monoid isomorphism: Track E handles that
separate obligation.
