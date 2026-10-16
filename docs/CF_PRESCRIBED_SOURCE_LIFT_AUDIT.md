# Adversarial audit: lift the prescribed finite embedding to a C_F stage

16 October 2026

## Exact source-fixing statement

The previously certified source theorem (PR #163) says that
a globally strictly d-closed *finite vertex set* S⊆M is
the image of a d-closed subset A of some finite stage U_n.

For genericity it is essential to retain not only that image
but the full embedding map e from the prescribed finite
graph into M. This module proves:

Given an induced injective e:S→M with globally d-closed image,
there exist n and an induced injective f:S→U_n such that

  birth_n(f(x)) = e(x)  for every original source vertex x,

and f[S]≤d U_n.

Each e(x) has a representative at stage n, by exact set-image
equality. The representative is *unique* because birth_n is
injective, so choosing representatives cannot alter the
induced graph. Injectivity and inducedness of f follow from
those of e and of the stage-birth map. Equality of the image
f[S] with the known d-closed set A is proved by applying
injectivity of Finset.image along birth_n.

## Five hostile mathematical checks

**1. Pointwise equality.** A graph isomorphism from S to
some closed stage subset is insufficient for an extension
property over a prescribed embedding e. The pointwise
equation birth∘f=e must hold for every x, and it is
a separate field in the theorem.

**2. Choice uniqueness.** Representative selection uses
classical choice but is semantically unambiguous: two
stage representatives with the same birth label are equal.
No quotient choices or uncontrolled relabelling are used.

**3. All nonedges.** The lifted map must be *induced*,
not just graph-homomorphic. The proof composes the
input two-way adjacency equivalence with the previously
certified exact inducedness of each finite stage.

**4. Strict closure.** A finite image is not automatically
globally or even relatively d-closed. The theorem starts
with global strict closure of e[S], uses the existing
source-image closure theorem, and proves literal equality
of stage images before transporting the strict closure.

**5. Precise remaining work.** This prepares the entire
old source embedding for one-step extension. The next
bridge must still restrict f to the canonical support P,
obtain the actual named support equivalence P≃f[P]
(PR #171), normalize the full split local graph and
prove its size bound, then use the certified global
named-code response. The theorem does not assume an
embedding of the fresh part into the current stage.

All five roles are internal separated adversarial proof
checks, not external independent human referees. A
manuscript marker must remain provisional until final
Lean compilation, standard axioms and placeholders pass.
