# Track C: strong homogeneity via the existing strict back-and-forth

**Status:** proposed theorems on draft PR #437, pending exact-head
Lean kernel build, standard-axiom audit and no-placeholder check.
This is a mathematical adversarial review with role-separated
checks, not independent external human referee reports.

## Theorems and source

1. `CFDClosedBackAndForth.strictHomogeneous_of_finiteDClosedResponses`
   starts the *existing* finite strict joint-step recursion from an
   arbitrary initial `PartialIso M M`. It produces an induced
   automorphism extending that finite partial isomorphism literally
   on the original finite source.
2. `CFCoherentTower.publishedBirth_relabelled_strongHomogeneous`
   specializes to the **actual** published canonical `C_F` birth
   graph after a supplied genuine `ℕ ≃ PublishedBirthVertex`.
   It reuses the previously certified exact published growth
   restriction and complete countable finite response criterion,
   with finite restricted-class free joins explicit.

## Adversarial referee panel

**R1: Strict versus weak closure.**
The input is the `CFDClosedBackAndForth.PartialIso` structure:
both finite domains are `IsGloballyDClosed`, not merely
`IsGloballyStrong`. The same strict invariant persists along
the entire finite recursion. A weakly strong partial map cannot
be substituted into the proof.

**R2: Initial-map agreement.**
The previously proved theorem
`PartialIso.equivOfJointSteps_initial` states equality of the
total union map with the original equivalence on each source
vertex. Starting at a newly chosen empty partial map would prove
uniqueness but **not** homogeneity. This proof starts at the
user-supplied `p`.

**R3: Two-sided exhaustion.**
`PartialIso.hasJointSteps_of_finiteDClosedResponses` performs
both a forth and a back extension at every stage. Source and
target eventually cover all natural numbers. A one-sided
extension would only give an induced self-embedding, not an
automorphism.

**R4: Edges and nonedges.**
The finite response is induced (an `iff`), and the
coherent-union theorem yields a global `adj ↔ adj`. No
edge-preserving-only homomorphism is used, and distinct vertices
remain distinct because the union is an `Equiv`.

**R5: Published domain and free amalgamation.**
The birth specialization uses the exact restriction to natural
cardinalities of the paper's `F : ℝ≥0 → ℝ≥0`.
`hFree` is an independent `HasFiniteClassDClosedFreeJoins`
hypothesis; it is *not* derived from monotonicity.
Continuity, strict empty-base closure and singleton membership
are not needed **once a genuine enumeration is supplied**;
they are needed earlier in the manuscript to derive the
existence of that enumeration.

**R6: Countable carrier.**
The specialized theorem assumes `ι : ℕ ≃ PublishedBirthVertex`,
rather than turning mere countability into infinitude. Under
the standing empty-base and singleton assumptions this `ι`
already exists by merged Track C PR #420; its existence is
not being silently assumed from a `Countable` instance.

**R7: Scope of homogeneity.**
The proved automorphism is for the *graph reduct*. The final
`publishedBirth_strongHomogeneous_onCarrier` theorem conjugates
the numbered automorphism by the supplied genuine carrier
equivalence; its output is an actual automorphism on the literal
birth-labelled vertex type and its initial-value clause is
transported pointwise. The proof does not assume that the
enumeration itself is an automorphism or order-preserving.
The automorphism does not necessarily preserve the enumeration
order or the functions `R,H`. It is not a theorem about finite
unique level lifts, the embedding monoid, Ramsey degrees,
or topological Ramsey spaces.

**R9: Conjugation direction.**
The native automorphism is `ι.symm.trans (e.trans ι)`,
so its value on `ι x` is precisely `ι (e x)`.
The opposite conjugation would not typecheck, and mere
injectivity of `ι` would not give an automorphism on the whole
birth carrier. The proof uses the explicit two-sided equivalence,
and applies the finite source agreement after computing the
conjugate.

**R8: Dependency and trust.**
The generic theorem invokes only already established strict
joint steps and coherent union. The canonical specialization
uses the existing exact countable birth recognition theorem,
not an isomorphism with a comparison `M_F`.
All three endpoints are to be checked by isolated `#print axioms`
and full Lean CI. A pending/failed build remains **unverified**
regardless of the strength of the paper proof.

## Negative controls

A finite strong map which is not *strictly* `d`-closed does not
meet the input invariant. A homomorphism reflecting no nonedges
cannot be extended by the induced partial-isomorphism recursion.
An arbitrary injection into a countable birth carrier cannot
replace `ι`, because it need not cover the target vertices and
may not reflect global strict closure.

No manuscript marker should be promoted before the exact-head
kernel checks and the statement-to-paper audit succeed.
