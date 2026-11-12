# Track B: literal request recognition — adversarial review

12 November 2026. These three lemmas recover actual finite-stage
request data from sets of literal birth-labelled vertices. They
are intended as infrastructure for the pending arbitrary finite
unique level-lifting induction.

## Six adversarial referee checks

**Referee 1: actual old supports.** Two named old supports
at the same stage have the same countable birth image iff
they are identical as finite subsets of that stage; the
nontrivial implication uses `toVertex_injective`.
Equal support sizes, or abstractly isomorphic supports, do
not imply the required literal equality.

**Referee 2: entire birth blocks.** Request-tag injectivity
requires equality of the FULL finite blocks at one fixed
birth level. It is not enough that two vertices have the
same ordinal or that blocks are isomorphic.

**Referee 3: nonempty code.** The proof extracts the first
fresh vertex `birthRoot F K n r`, which exists by the
`fresh_pos` certificate for actual local requests. A
hypothetical empty block would not determine a request tag
from equality of empty vertex sets.

**Referee 4: dependent request labels.** Birth vertices
are dependent pairs `⟨n,⟨r,i⟩⟩`. Their equality at the
same level forces equality of their actual request tags,
not merely equality of their ordinal indices. No
proof-irrelevant request fields are dropped.

**Referee 5: numerical size.** The cardinality theorem
relies on literal full-block equality and on the
kernel-checked `birthBlock_card` result; the equality
of code sizes is a consequence, not a separate
cardinality preservation hypothesis.

**Referee 6: mathematical boundary.** A request is not
determined by old named support and fresh size alone.
Its complete ordered adjacency matrix also matters.
These lemmas cannot establish an arbitrary embedding's
target code without an induced local coordinate map.
The full finite uniqueness, composition/restriction,
and monoid theorems remain unproved.

All three endpoints require exact-head Lean kernel checks,
the repository's ordinary axiom audit and placeholder scan.
No new manuscript validation marker should be promoted.
These are role-separated internal adversarial audits, not
independent external referees.

```sh
lake build BigHrushovski.CFBirthRequestTagRecognition
lake env lean CheckAxiomsCFTrackBRequestTagRecognition.lean
python3 scripts/check_no_placeholders.py
```
