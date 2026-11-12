# Track B: arbitrary finite unique-level lifting — adversarial audit

12 November 2026. This file is stacked on the arbitrary one-block
uniqueness proof, PR #479. The exact-head Lean kernel and axiom
audits are required before any theorem is called validated.

## Mathematical statement

Let s be an arbitrary finite b-closed subset of the countable
birth-labelled C_F structure. Let e,g be arbitrary injective induced
maps on precisely s, preserving complete b-values, birth-level
preorder (both directions) and canonical birth order (both directions).
If e and g assign the same target birth level to EACH vertex of s,
then e=g. In particular, this holds whenever both maps realize the
same prescribed assignment h on the finitely represented birth
levels of s. Values of h outside that represented set play no role.

## Six adversarial referee roles

**Referee 1 — induction on actual birth levels.** A source vertex
has a unique natural-number birth level. Strong induction on this
number is well founded; it does not need every earlier level to
be represented. Hence gaps in the source pose no special case.
The empty finite source is included vacuously.

**Referee 2 — inductive data genuinely available.** At source level
n, the induction hypothesis grants e(z)=g(z) only for z∈s with
birth level less than n. It does NOT provide agreement on all of
the possibly much larger old finite stage U_n. The one-block
lemma uses precisely this restricted agreement.

**Referee 3 — same target stage.** The target birth levels for
the selected source vertex agree because of the hypothesis
that both maps realize the same assignment on represented
source levels. Dependent target request tags are compared
only AFTER rewriting the equality of target stage indices.
There is no assumption of a globally increasing map ω→ω.

**Referee 4 — complete request rigidity.** The one-block proof
derives exact named support images, fresh sizes, and complete
ordered adjacency matrices including nonedges. It proves
literal equality of the target request tags and then of the
fresh ordinals. There is no assumption that e or g is the
canonical recursively constructed lift.

**Referee 5 — order and function language.** Both maps preserve
and reflect the actual canonical birth order and level preorder
and preserve all complete b-values. These hypotheses are
required; mere graph embeddings or one-sided positive edges
would not supply uniqueness. Translation to the manuscript
R/H language must be justified separately using the verified
finite closed-source equivalence.

**Referee 6 — remaining results and trust boundary.** This
integrated theorem establishes AT MOST ONE such finite
b-functional embedding for a prescribed assignment. To obtain
the manuscript's existential/unique R/H lemma, combine it
with the previously kernel-verified finite R/H existence
theorem and the verified closed-source b↔R/H equivalence;
then prove restriction/composition compatibility. The
countable self-embedding monoid is a separate limit step.
No LaTeX validation marker is changed before exact-head CI
and subsequent R/H integration.

These are six internal adversarial review roles, not six
independent human referees.

## Exact mechanical gate

```sh
lake build BigHrushovski.CFArbitraryFiniteUniqueness
lake env lean CheckAxiomsCFTrackBArbitraryFiniteUniqueness.lean
python3 scripts/check_no_placeholders.py
```
