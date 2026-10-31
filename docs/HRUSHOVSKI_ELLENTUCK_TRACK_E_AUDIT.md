# Track E: concrete Ellentuck copy spaces — adversarial validation (1 November 2026)

Source manuscript: `janhubicka/The-big-Hrushovski`, main `264bc23505f2c6c9fda83b544edf55badcd120b2`;
Section 6 and subsections 6a–6c. Lean baseline:
`janhubicka/lean-big-hrushowski`, main `1f5fcd06fe6fcdbfdfeab997125b31609df98b38`.
The Track A split and certification rules are in PR #266
(`docs/ADVERSARIAL_AUDIT_PARALLEL_TRACKS_20261031.md`).

This document is a **role-separated internal adversarial mathematical review**,
not a report from independent human referees. Until CI succeeds, the new
Lean lemmas are **submitted for checking, not certified**.

## Existing exact abstract infrastructure

- `janhubicka/lean-ramsey-space-todorcevic`, main
  `ae275646478829dacfdcd5103d7993b03f6c7688`:
  `RamseySpace.abstractEllentuck_textbook`,
  `AbstractRamseySpace.ofPublishedAxioms`,
  `ApproximationSystem.IsTychonoffClosed`, and
  `RamseySpace.Examples.Ellentuck.classicalEllentuck`.
- The classical Ellentuck instance uses points `ℕ ↪o ℕ` and first-n
  increasing values. Both the refinement order and finite approximations
  must be preserved, not only the abstract set of points.
- The separate `RamseySpace/EquivTransport.lean` Track E branch transports
  *all* data along a genuine equivalence of points and proves A.1–A.4,
  Tychonoff closedness and the textbook conclusion for the transported
  space. A future concrete copy-space equivalence remains an assumption
  until proved in Track E using Track B.
- The concrete `HrushovskiEllentuckSupport.lean` proves finite-support
  saturated range identities, monotonicity, intersection, singleton
  witness reflection, and dependency closure **without** using any
  unverified level-lifting theorem. The status of each is decided by
  `CheckTrackE.lean` and its dedicated CI, independently of the umbrella.

## Three spaces, exact theorem dependencies

| Copy space | Approximation and reduction | Proof route | Still needed for exact certification |
| --- | --- | --- | --- |
| `R_0` | Whole first n *closure components*; inclusion | Direct A.3(2) and A.4 via complete unary closure | Concrete type and finite approximations in Lean; the complete finite functional age and tail-extension theorem from Track A; proper A.2(3); relative A.4; closed code image |
| `R_F` | Full critical-height *induced diagrams* of a fixed rational diagonal coding antichain; inclusion of closed lifted ranges | Explicit isomorphism to Dobrinen's rational `D(D)` | Unique finite/countable level lift from Track B; similarity reconstruction (including diagonal pairs); exact restriction of Devlin and induced coding trees; formalization or carefully delimited external hypothesis for Dobrinen 6.4; all topology correspondences |
| `R_ω` | First n represented *image levels*; inclusion | Equivalence with classical Ellentuck space | Track B's unique lifted `Inc(ω)` action, composition and complete range formula; exact equivalence with `ℕ ↪o ℕ` and approximation-respecting map |

### Dependency boundaries

**No current Track E code certifies the manuscript's Theorem `ell:thm:main`.**
The abstract Ellentuck theorem is reusable *once* a concrete structure
satisfies the axioms and closedness. Do not change theorem validation
markers to green using only the abstract theorem or these unconditional
finite-support calculations.

For `R_0`, the manuscript's tail-extension lemma
`lem:C0-tail-extension` uses `prop:C0-free-generic`; the Lean finite
functional limit is a Track A task. The direct deletion/splicing argument
for A.3(2) is not an abstract consequence of amalgamation of the finite age.

For `R_F`, Theorem 6.4 of Natasha Dobrinen,
*Infinite-dimensional Ramsey theory for homogeneous structures with
SDAP+*, arXiv:2203.00169v3, includes the rational coding-antichain
spaces as topological Ramsey spaces. Theorem 6.3 alone is only the
metric-Borel Ramsey conclusion. Exact transfer of the full A.3(2),
A.4, metric and Ellentuck topologies must use the stronger theorem and
the actual coding-tree similarities, **not** finite-level colourings.

For `R_ω`, an order isomorphism
`[ω]^ω ≅ R_ω` is insufficient unless the first-n increasing values
are shown to coincide with the chosen first-n image-level
approximations. This is why the reindex interface pulls back the
approximation map explicitly.

## Referee passes and controls

**A.1/A.2 referee.** The manuscript counts complete components rather
than individual vertices; the empty approximation and empty level sets
need separate checks. In `lean-ramsey-space-todorcevic`,
`Finitization.prefix_leFin` uses *reflexive* `IsInitial`,
and the `EllentuckFinitization.prefix_leFin` proof takes `d=c`.
The literal published A.2(3), reproduced in Section 6, requires
`a ⊏ b` and `d ⊏ c`. This is a **source-to-Lean interface discrepancy**:
do not claim that the formal field alone verifies the strict
published clause. The separate Track E file
`RamseySpace/Examples/EllentuckProperA2.lean` gives a proof of the
literal proper-prefix clause for the *classical* Ellentuck space,
pending CI. This does not imply a logical inconsistency of the abstract
library: the library may prove a stronger conclusion from weaker
hypotheses.

**A.3 referee.** Let `C=r_d(Y)`, `D=C\\a`. The text's intermediate
`W=X ∪ {v : Γ(v) meets D}` need not be closed. The passage to
`V={v∈Y : Γ(v)⊆W}` is indispensable. It retains the entire ambient
depth prefix, while every closed copy with stem `a` avoids `D`.
A weaker amalgamation ideal or ordinary free amalgamation would not
suffice. The finite counterexample in `notes/ellentuck/VERIFICATION.md`
(components with closures `{0},{1},{2},{0,2,3}`) witnesses the
non-closedness of `W`.

**A.4 referee.** Candidate components are selected by **complete**
ordered local type over the *actual* lower part `P_τ⊆a`.
One thins those components to an infinite monochromatic family,
deletes the other candidates and everything depending on them, and
retains the complete depth prefix. A global finite Ramsey theorem
does not supply this relative pigeonhole axiom. The original
text's proof uses the extension property, which is still a dependent
structural fact in the Lean pipeline.

**Functional-range referee.** For rational and omega levels,
`supportDomain σ S = {v : σ(v)⊆S}` is the required range candidate.
It is **not** the union of fibres `π⁻¹[S]`. To reflect inclusion
one needs actual singleton-level witnesses `z_q` with
`σ(z_q)={q}`. The new Lean result states this hypothesis, rather
than postulating its concrete realization. Closure is conditional
on the exact support-dependency transport hypothesis.

**Representation referee.** The coding similarity must preserve
both coding and splitting events, diagonal comparisons, initial
segments on each critical level, ancestry and left/right order.
The paper's `P` relation uses repeated entries to name coding
events. The construction of these induced trees remains
unformalized in Track E.

**Certification referee.** Audits must compile the new
non-umbrella modules explicitly. The separate `CheckTrackE.lean` and
branch-specific workflow enforce this. No `sorry`, admitted local
axiom, unverified totalization from a partial old-source map, or
external theorem imported as a hidden hypothesis is acceptable in
a green endpoint.

## Work order

1. Compile and audit the unconditional finite-support calculus and
   classical proper-prefix A.2; then merge the reusable transport library.
2. Formalize an abstract `ClosureComponentCopy` interface with complete
   one-generated closure, ordered block fibers and tail extension.
   Prove the manuscript's A.3 and A.4 arguments at that interface;
   instantiate only after the Track A C0 functional generic is certified.
3. For `R_ω`, import the *exact* unique-level-lift theorem from Track B
   and give the equivalence to `ℕ ↪o ℕ`, with a proof that the finite
   approximations are the first represented levels.
4. For `R_F`, build a separate similarity/critical-frontier
   equivalence and record Dobrinen's theorem as an external,
   explicitly marked dependency unless a Lean formalization is
   available. No surrogate use of `lean-milliken` proves it.
5. Only after all three concrete instances have exact theorem
   declarations, passing CI and axiom audits, promote the manuscript
   Section 6 validation markers.

No changes to mathematical prose or global manuscript markers are
made by this Track E audit branch.
