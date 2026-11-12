# Track B: restrictions of actual prescribed finite lifts

12 November 2026. The target is the restriction-compatibility
clause of the finite C_F unique-level-lifting lemma.

## Main result

Let s⊆t be finite b-closed subsets of the actual birth carrier,
and let level be strictly increasing on birth levels represented
in t. Construct the prescribed lifts of t and s, using
arbitrary potentially different finite stage covers nT and
nS. The restriction of the lift of t along literal inclusion
s↪t is exactly the lift of s with the restricted level data.

## Six independent adversarial referee roles

1. **Source is genuinely closed:** Complete b-values of each
   x∈s belong entirely to s. The precursor theorem
   `finiteSourceBirthBValue_inclusion` is an equality
   of complete values, not an inclusion. Otherwise the
   restricted map could fail to preserve the unary operation.
2. **No total finite-stage map:** The restricted function is
   obtained by composing the actual lift on t with the
   literal inclusion of the selected finite source s.
   No unselected vertex of a complete old stage is mapped.
   The two target finite stages can even be different.
3. **Embedding conditions are complete:** The restriction
   inherits injectivity, induced adjacency including
   nonedges, the canonical order, the reflected birth-level
   preorder and the exact prescribed birth labels.
   The complete unary b-value preservation uses the new
   restriction lemma, not a hand-waved substructure claim.
4. **No global level assignment:** The assignment need only
   be strictly increasing on levels represented in t,
   hence also on those represented in s. Empty sources,
   gaps in the represented levels, and first-level target
   zero are included.
5. **Correct use of uniqueness:** The kernel-verified
   arbitrary finite uniqueness theorem compares the
   restricted lift with the independently constructed lift
   of s. No equality of two recursive stage-by-stage
   choices is asserted directly or assumed.
6. **Remaining finite and infinite goals:** This lemma
   proves restriction compatibility in the auxiliary
   b-language; the actual R/H language follows from the
   verified closed-source equivalence, but an explicit
   formal corollary is still needed. Composition
   compatibility and the countable monoid remain open.
   No manuscript validation marker is promoted on
   this standalone PR.

Internal adversarial roles, not external human referees.
Exact-head Lean CI, standard axioms, placeholder scans and
finite regressions are mandatory.

```sh
lake build BigHrushovski.CFPrescribedFiniteLiftRestriction
lake env lean CheckAxiomsCFTrackBPrescribedRestriction.lean
python3 scripts/check_no_placeholders.py
```

## Integration recheck (12 November 2026)

This PR now targets `main` after the finite arbitrary-map uniqueness
module (PR #481) and exact closed-source b-value restriction module
(PR #498) were merged there. Its earlier isolated-branch general
CI failed at import resolution because the source branch predated
PR #481; this is not a kernel certificate. The updated merge head
must pass a new exact Lean/axiom/placeholder build before integration.
