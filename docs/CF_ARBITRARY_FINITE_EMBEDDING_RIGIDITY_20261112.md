# Track B: arbitrary finite embedding rigidity — 12 November 2026

This is a new lemma family for **arbitrary** finite \(\mathcal C_F\)
embeddings. It must not be conflated with the previously merged
existence proof of one specially constructed prescribed lift.

## Exact mathematical contribution

For a finite source \(s\), a genuinely partial map
\(e:s\to M_F^\dagger\) preserving complete restricted auxiliary
\(b\)-values and reflecting the birth-level preorder carries the
**entire named support** and **entire fresh block** of any source
vertex exactly onto the support and block of its image. No
unproved whole-block-surjectivity premise is introduced.

If \(s\) is closed under complete \(b\)-values and \(e\) also
preserves and reflects the actual canonical birth order, then it
fixes each internal finite ordinal of each birth block. This
applies to arbitrary embeddings, not just the constructed lift.
A second endpoint obtains the same ordinal conclusion from the
complete \((R,H)\) language, including reflection of the partial
domain of \(H\), via the previously proved equivalence on closed
source subsets.

## Six independent adversarial referee roles

**Referee A — partial-domain correctness.** The map is defined
only on `SupportCarrier (Vertex F K) s`. The support/block theorem
uses `finitePartial_birthSupport_block_of_preorder` and
`selectedFiniteSet`, not a total graph self-embedding.
The arbitrary extension in later lemmas is by identity outside
`s` and is used only to evaluate complete finite-set images.
No graph or function property is imposed outside `s`.

**Referee B — exact, not one-sided b-values.** The premise
requires equality of the full image of each restricted unary
value with the **full target unary value**. Mere inclusion
would not prove target block surjectivity and would invalidate
ordinal recovery. The condition `IsBirthBlockClosed F K s`
ensures the complete ambient `b(v)` lies in `s`, so the
restricted domain really contains the complete source value.

**Referee C — level-preorder reflection.** Strictly increasing
target assignments in the previous existence theorem imply
preservation *and reflection* of the birth-level preorder.
The generic ordinal theorem explicitly assumes both directions;
preservation alone would not distinguish the target top block.
No strictly increasing map on all natural-number levels is assumed.

**Referee D — the actual canonical order.** The source-local
ordinal result requires the manuscript's recursively constructed
`canonicalBirthLt`, not arbitrary chosen root orders.
A bijection of unordered complete birth blocks can permute
positions. Order preservation together with full block
surjectivity excludes these permutations.

**Referee E — R/H domain discipline.** The RH endpoint assumes
all *defined* H-images and reflection of the domain (root-set
criterion), then uses the exact existing equivalence to obtain
all auxiliary b-values. H is NOT silently treated as total.
The conclusion is only the block ordinal, not yet agreement
of complete target request tags.

**Referee F — mathematical scope and proof trust.** The finite
uniqueness theorem still requires comparison of complete
**ordered local adjacency matrices** of arbitrary target
requests, using inducedness, support equality and block
ordinal rigidity. It then needs induction through represented
birth levels and validation that skipped source/target stages
do not introduce additional choices. These four lemmas do not
settle that. Kernel checking of each named endpoint and the
standard-axiom/placeholder audits must pass before changing
manuscript validation markers; internal role reviews are not
external human refereeing.

## Mechanical verification

```sh
lake build BigHrushovski.CFArbitraryFiniteEmbeddingRigidity
lake env lean CheckAxiomsCFTrackBArbitraryFiniteRigidity.lean
python3 scripts/check_no_placeholders.py
```

The repository's umbrella Lean workflow discovers the new exact
axiom check file and runs all ordinary regressions. This review
was written in parallel with the source and is not a kernel
certification. Do not merge until exact-head CI is green.

## Next lemma for finite uniqueness

Fix a represented source level \(n\) and its target level \(m\).
Suppose two admissible finite embeddings agree on all source
vertices born before \(n\). Their complete old-support images
then agree, and the present ordinal theorem fixes all positions
in each source birth block. It remains to prove the *complete
adjacency matrix* of both actual target request tags equals
the matrix of the uniquely transported source request. Use
`request_eq_of_support_size_adjacency` after deriving equality
of support, size and **all** adjacency bits. This will prove
agreement on the new level, completing a finite induction.
