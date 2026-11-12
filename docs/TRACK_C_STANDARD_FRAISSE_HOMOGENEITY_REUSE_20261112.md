# Track C — factor strong homogeneity through the ordinary Fraïssé presentation

**12 November 2026. Status:** candidate Lean source. The exact-head isolated
build, standard-axiom and placeholder checks, and full Lean CI are required
before calling this verified. These are internally separated adversarial
checks, not reports by external referees.

## Mathematical change

The existing `publishedBirth_strongHomogeneous` theorem was proved by
selecting the published birth enumeration and calling a one-off numbered
birth automorphism. The new general theorem

`CFDClosedBackAndForth.standardStrongFraisseLimit_homogeneous`

states instead that *any* graph on an arbitrary carrier with a
`StandardStrongFraisseLimitPresentation` is strongly homogeneous for
finite induced globally strictly `d`-closed partial isomorphisms.

The proof first derives the three finite recognition facts from the
**already verified** conversion
`StrongFraisseLimitPresentation.toPresentedFraisseData`. It then applies
the existing native finite-subtype transport
`nativeHomogeneity_of_numbered`, and the existing strict joint-step
recursion `strictHomogeneous_of_finiteDClosedResponses`.
The final `Equiv` on the original carrier is the conjugate of the
numbered automorphism.

The published birth-graph theorem is retained *with exactly the same
statement*, but its proof is reduced to direct application of the general
theorem to the independently constructed birth Fraïssé presentation.
No manuscript TeX is changed.

## Adversarial referee panel

**1. Generality and assumptions.** The general theorem takes
`StandardStrongFraisseLimitPresentation F G` for a graph `G` on
*arbitrary* `V`, and no published-growth, `F(0)=0`, singleton, or
free-amalgamation hypothesis. Those class assumptions are needed to
*construct* the birth presentation, not to deduce homogeneity from it.
It would be invalid to add an `IsGloballyDClosed ∅` assumption to
the generic theorem merely because the previous uniqueness argument
started its recursion from the empty map.

**2. Strong versus strictly closed.** Source and target finite subsets
satisfy `IsGloballyDClosed` in the entire model. Only the inherited
`HasFiniteDClosedIntervalResponses` is used to advance the back-and-forth;
no reduction to weak strongness occurs before the final induced union.

**3. Old values.** The input finite map is an `Equiv` between literal
subtypes of the original `V`. The old theorem
`nativeHomogeneity_of_numbered` transports that map exactly and
proves that the returned original-carrier automorphism agrees at every
specified source vertex. A mere existence of an isomorphic copy would
not establish this clause.

**4. All finite sources.** The ordinary finite extension property
quantifies over arbitrary finite graph carriers, not only linearly
ordered sources, natural intervals or canonical stage cuts. The
conversion `HasStandardFiniteDClosedExtensions.toNatIntervals` was
previously certified and preserves the entire induced graph,
including nonedges and the literal old values.

**5. Two-sided totality.** The strict joint-step theorem exhausts both
source and target; its union is a bijective `Equiv`, not just an
induced injection. The initial map is retained by the existing
`PartialIso.equivOfJointSteps_initial` theorem.

**6. Non-circularity and reuse.** The conversion from standard
Fraïssé data to the three finite recognition facts uses no new
countable isomorphism. In the birth specialization, the data are
constructed by merged PR #420 independently of the birth-versus-`M_F`
comparison. The refactoring reuses the generalized theorem rather
than copying the back-and-forth or the previous specialized
conjugation proof.

**7. Scope.** Homogeneity is proved in the graph language for finite
globally strictly `d`-closed induced subgraphs. It does not assert
preservation of the birth order or the extra functions `R,H`,
the finite unique level-lifting property, embedding-monoid
identification, big Ramsey degrees or Ellentuck conclusions.

**8. Trust and source changes.** The existing published birth
homogeneity theorem's type is left byte-for-byte unchanged. The PR
changes its proof and inserts one general theorem in the same module,
plus a new exact axiom endpoint. No `sorry`, `admit`,
`native_decide`, new `axiom`, external class assumption or
manuscript green marker is introduced. Exact-head kernel checks
must verify this.

## Check plan

Run the dedicated `track-c-native-finite-homogeneity.yml` workflow
and full `Lean` workflow on the same PR SHA; check
`#print axioms` for the general theorem and unchanged birth theorem;
scan placeholders, review complete diff, and merge only after
all conditions pass.
