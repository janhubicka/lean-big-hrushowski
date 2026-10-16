# Adversarial audit: literal finite-stage source for a global closed copy

16 October 2026

## Main theorem and why it matters

Given a finite vertex set S in the birth-labelled countable graph
M that is globally strictly d-closed in M, find an actual stage
U_n and a finite A⊆U_n such that S is *literally equal* to the
birth image of A and A<=d U_n.

By common finite-stage coverage, choose U_n containing S.
Let A consist of precisely those vertices of U_n whose birth
labels lie in S. The stage birth map is injective and its whole
image contains S, so birth[A]=S. Since S is globally d-closed,
its inclusion S<=d birth[U_n] is strict. The induced stage
embedding then reflects this d-closedness to A<=d U_n.

This theorem is deliberately stated with equality of the
vertex set, not just existence of an isomorphic finite source.
It permits the next minimal-response argument to extend the
*prescribed* copy of the source.

## Five adversarial mathematical checks

1. **Same named vertices.** An arbitrary isomorphic copy of S
   in a stage would not suffice for the extension property
   over a fixed embedding. Pullback via the actual canonical
   birth map guarantees literal equality of images.

2. **One stage for all vertices.** Pointwise stage coverage
   does not suffice; the theorem uses the certified common
   finite-stage coverage from PR #160.

3. **No spurious edges.** A graph homomorphism cannot reflect
   d-closure because extra edges change predimension. The
   exact induced embedding theorem is PR #159, and the
   finite d-closed transport theorem compares all
   intermediate subsets.

4. **Global-to-local direction.** Global strict d-closedness
   restricts to the chosen finite image before transport.
   The argument does not falsely infer that every finite
   vertex set S is d-closed: the global-closure hypothesis
   is essential.

5. **No accidental response theorem.** This is only the
   source-preparation half of the full finite extension
   property. One must still normalize the desired minimal
   extension into an admissible local request over its
   *actual* support, prove the explicit K size bound, and
   use the countable response statement of PR #162.

Negative control: without globally strict d-closedness of S
the pullback A may be merely an induced graph subset but
need not be d-closed in U_n.

The five roles are separated internal mathematical reviews,
not external independently spawned referee agents. No
manuscript GREEN marker is permitted without passing
Lean CI, standard-axiom checks and placeholder scan.
