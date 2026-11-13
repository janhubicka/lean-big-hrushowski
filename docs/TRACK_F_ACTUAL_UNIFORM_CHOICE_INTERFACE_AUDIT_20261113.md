# Track F — passing from the generator fibre to the actual next-SCC choices
13 November 2026

Stacked on PR #519. The separate PR #517 is designed to
discharge the single explicit generator-equivalence hypothesis.
No TeX or manuscript validation-marker changes.

## Finite theorem

For an actual SCC B, fix a legal SCC ranking r and any complete
context of internal SCC orders. The generator-fibre count
submitted in PR #519 gives exactly g_A(B) choices of the
new order on B when canonicality is tested at one chosen generator.

The *original* concrete next-component choice set of PR #497
uses the stronger predicate \`IsCanonicalAtComponent\`, which
checks every generator x in B.

The theorem \`canonicalNextComponentChoices_card_of_generatorCriterion\`
states precisely the necessary bridge. Assuming that for every
new internal order of B the all-generators test is equivalent
to the test at the chosen generator, it proves

\[
  |\operatorname{Next}_r(\mathbf e,B)|=g_A(B).
\]

The proof is an exact equality of two finite sets of labelled
component orders followed by the previously proved generator-fibre
count. It also yields the same cardinality for the finite set
of whole assignments obtained by updating B, since the update
is injective.

The generator-equivalence hypothesis is **explicit** in the Lean
statement. It is not claimed as an already certified theorem
in this branch. The independent PR #517 will supply it.

## Internal adversarial referee panel

1. **Original predicate.** The codomain is PR #497's actual
   all-generator next-choice set, not a newly invented numeric
   surrogate.
2. **Hypothesis visibility.** The equivalence between testing
   one generator and all generators is an explicit proposition;
   no unverified lemma is smuggled in as an axiom.
3. **Labelled orders.** Both sides consist of bijections
   enumerating the actual SCC B; no quotient by automorphisms
   or isomorphisms is taken.
4. **Context.** The statement covers all complete contexts,
   including those not satisfying earlier canonicality tests,
   provided the SCC ranking is legal.
5. **Correct factor.** The factor g_A(B) is the induced
   pointwise lower-part stabilizer, not the ambient
   automorphism group.
6. **Assignment update.** Updating one SCC is injective;
   counting whole updated assignments gives the same number
   as counting the new internal B orders.
7. **Certification.** Dedicated Lean build, named theorem
   axiom audit, placeholder scan and independent exhaustive
   finite generator-invariance tests must all pass. These
   role-separated checks are internal, not external refereeing.

## Still open

Once PR #517 is certified and merged, its theorem can be used
to instantiate the displayed hypothesis and obtain the
**unconditional** uniform actual next-fibre count.

There remains one independent finite integration step:
identify reachable length-i histories of tagged SCC-order
choices with the canonical rank-i prefixes of the actual
SCC assignments. The certified locality theorem #492
shows future choices cannot change earlier canonicality.
The reachable-history product lemma #482 then yields the
rank-specific product; the exact actual-order data count
#488 sums over the legal SCC rankings.

Neither the finite global product nor the infinite N₀ big
Ramsey theorem is claimed here.
