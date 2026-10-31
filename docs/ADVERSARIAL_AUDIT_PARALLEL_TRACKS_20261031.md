# Adversarial audit and independent proof tracks (31 October 2026)

Manuscript: `janhubicka/The-big-Hrushovski`, v52, main `264bc235`.
Lean baseline: `janhubicka/lean-big-hrushowski`, main `1f5fcd06`.
This is an **internal, role-separated adversarial review**, not an externally recruited panel. A successful build and a standard-axiom audit certify the stated Lean theorems, **not** their identification with all statements of the paper.

## Findings, ranked by risk

### P0 — genuine partial source in the finite C_F level lift

At `sections/03b_enumeration_CF.tex`, Lemma `CF-coordinate-pattern` maps only the already represented old substructure
`S=A_{<i}` into the target stage `V=U_{s_i}`. The source's entire old stage `U=U_{t_i}` need not map into `V`.
Take `U={u}`, `S=V=∅`: the required partial embedding `S→V` exists, but **no total function `U→V` exists**.

The green citations to
`CFActualRequestOrderTransport.transportGrowthStageRequest_order_iff` and
`transportGrowthStageRequest_reflects_eq` concern a *total* `f : U → V` with `StrictMonoOn f S`.
That is not the partial theorem used in the paper. Similarly, the total-domain
`CFSelectedBatchBValues.selectedGrowthBatchMap_bValue_image`,
`CFActualSelectedBatchMap.selectedGrowthBatchMap_{injective,dClosed_full}`,
`CFActualSelectedBatchInduced.selectedGrowthBatchMap_induced`, and
`CFSelectedBatchStageOrder.selectedGrowthBatchMap_stageOrder_iff` have no such partial-source conclusion.

The corresponding paper PR changes those **seven** local green markers to orange and places an orange marker on the entire finite-lifting lemma. The underlying total-map theorems remain correct and checked; this is a certification-scope repair.

The genuinely partial components already present on main include
`CFPartialOldSourceRequest`,
`CFPartialTagNoncollision.selectedGrowthBatchMapSubtype_injective`, and
`CFActualSubtypeSelectedBatch.selectedGrowthBatchMapSubtype_dClosed_full`.
Open [PR #264](https://github.com/janhubicka/lean-big-hrushowski/pull/264) adds actual partial-domain *inducedness* and complete fresh-block `b`-values; [PR #265](https://github.com/janhubicka/lean-big-hrushowski/pull/265) (draft at review time) adds strict comparison of literal support tuples. Branch CI is passing but both PRs were open and returned `mergeable=false` in a later API query. Do **not** describe either result as merged into the manuscript's Lean source pin.

Still missing: compose the complete partial request-key comparison, actual partial **stage order**, complete value preservation for old and new vertices, and induction through represented levels; then prove **uniqueness**, restriction/composition, and the infinite lift. The `CF-embedding-monoid` theorem must not be green before these.

### P1 — C_0 finite functional age and countable reduct

`C0TaggedSharedBaseValues.taggedCanonicalValues_both_of_named_base` verifies **both** complete original unary values in the tagged free graph; `C0TaggedMinimal` separately gives minimal strong increments, and `C0FiniteStrongSpanFunctional.exists_canonical_functional_strong_amalgam` lifts an arbitrary finite strong *graph* span, retaining the left functional structure.

The remaining finite task is to package the explicit joined chronology with both unary-value and all-minimal-step conclusions as **one theorem**, for arbitrary finite functional objects sharing a closed base. It is not legitimate to assume matching component orders on that base. Keep the first factor's chronology fixed; frontload the second factor's common closed base and append its fresh components. The complete values determine the component partition and orientations of edges within the base.

Then construct the functional Fraïssé limit and prove its reduct has finite strong covers and the strong graph extension property. This is stronger than the finite graph-to-functional lifting lemma. The manuscript's `prop:C0-free-generic` must remain partial meanwhile.

### P1 — C_F countable identification

`CFRealFiniteGenericity.finiteRealDClosedInterval_globalResponse` supplies arbitrary labelled finite strict `d`-closed responses using the canonical growth inverse. It assumes the finite source belongs to `C_F`. The level tower and growth membership are established using the **standing `d`-closed free-amalgamation hypothesis**; neither the real-growth monotonicity conditions alone nor genericity of an unrelated countable graph substitute for this.

Package the class membership, global `d`-closed stage coverage, literal extension property and strong-limit uniqueness into one theorem with exactly the manuscript's hypotheses. The published `F:[0,∞)→[0,∞)` versus Lean `F:ℝ→ℝ` restriction needs an explicit adapter, e.g. `x ↦ F(max(x,0))`.

### P1 — high-level theorems still downstream

`C_0` one-generated coordinate host, `C_F` degree one, the rational-level quotient with Devlin degrees, finite Ramsey statements and the **three concrete Ellentuck copy spaces** are not certified by the finite predimension modules. The abstract Ellentuck theorem in `lean-ramsey-space-todorcevic` is reusable, but the A.1--A.4 axioms and closedness of each concrete approximation space must still be proved.

### P2 — lower-risk semantic and annotation boundaries

`acl(X)=cl_s(X)` is argued in the paper by an induced finite diagram and an infinite-orbit argument. Lean verifies the finite induced-diagram image and finite stabilizer orbits, **not** first-order syntax and semantics of algebraicity; do not label the FO equality formally proved.

The published sparse-graphs orientation `successor-d-closure` is **not** the auxiliary enumeration `b`-closure. The manuscript already notes this; any shared abstraction must preserve the distinction. Likewise `C_0` closure-respecting orders are not the admissible-order expansion with the expansion property.

`scripts/check_no_placeholders.py` bans `sorry|admit|axiom|unsafe` in Lean sources. `scripts/check_axioms.py` admits only standard logical axioms among the **enumerated** `#print axioms` endpoints. Neither script establishes alignment with the English statements; add an exact statement-to-declaration registry. The blanket "no placeholders" scan does not itself prove that every source is imported by the umbrella module.

## Parallel tracks

Work in independent branches. Each track owns new proof files and its own audit log; avoid concurrent edits to `BigHrushovski.lean`, `CheckAxioms.lean` and `validation.tex`. Put imported endpoints and the global axiom audit into a small integration PR after the individual proof files have been reviewed.

| Track | Scope / file ownership | Exact deliverable | Dependencies |
|---|---|---|---|
| A — `C0-functional` | `C0*FinalAmalgam.lean`, `C0*FunctionalLimit.lean` | One exact two-sided tagged functional amalgam, then countable functional limit and graph reduct `M_0` | Existing C0 finite lemmas; independent of B–F |
| B — `CF-partial-lifts` | `CFPartial*Order.lean`, `CFPartial*LevelLift.lean`, `CFFiniteUniqueLift.lean` | Literal partial-source one-level induced ordered `b`-embedding and complete finite **unique** level lift; countable `Inc(ω)` action | #264/#265 APIs (after rebase/review); independent of A, C, E, F |
| C — `CF-generic` | `CF*LimitIdentification.lean`, `CFGrowth*Adapter.lean` | One countable strong-limit identification under exact published assumptions | Existing finite response/growth results; independent of B until final presentation link |
| D — `Ramsey-transfer` | `C0CoordinateHost*.lean`, `CFLevelRamsey*.lean`, `UFRational*.lean` | Conditional abstract-coordinate Ramsey transfers, then paper BRD and rational quotient results | Can prove generic transfer lemmas independently; concrete instances need A or B |
| E — `Ellentuck-spaces` | files in `lean-ramsey-space-todorcevic` and separate concrete `HrushovskiEllentuck*.lean` | A.1–A.4, metric closedness and approximation-to-copy identification for each of three spaces | Abstract theorem library; concrete code inputs require B/D; no dependency on F |
| F — `orientations` | `Orientation*Relative*.lean`, `N0ExactDegrees*.lean`, `NFSinkObstruction*.lean` | v52 `N_0` degree theorem and concrete `N_F` obstruction, separately from open `N_F` upper bound | Finite graph/orientation infrastructure; independent of A–E |
| G — `paper-integration` | `sections/*.tex`, `validation.tex`, audit notes | Exact scope of each green/orange/blue marker, prose shortening and PDF check | Independent editorial suggestions; promotion to green only after other track CI |

## Shared mathematical interfaces, not parallel reinventions

1. **Local free extension:** retain the existing identity `δ(A∪S)−δ(A)=δ(P∪S)−δ(P)` and its weak/strict and minimal-step consequences. This is already in the preliminaries and in Lean. Keep weak strongness and strict `d`-closure distinct in the interface.
2. **Minimal decomposition and root forcing:** reuse `finite_minimal_decomposition_of_{strong,dClosed}_absolute` and the corresponding root-forcing lemmas; do not manufacture a new canonical sequence of minimal increments.
3. **Support-transport record:** a finite named support, its induced graph, an ordered fresh block, the complete adjacency/nonadjacency matrix, and an injective map defined only on the **selected** source. The generic *finite-order* part of #265 can serve both C0 and CF without identifying their closure notions.
4. **Complete function transport:** state equality of full set-valued images, not mere forward inclusion; source closedness and reflection of partial-operation domains must be listed. The C0 orientation-invariance lemma and CF `b`-to-`R,H` dictionary are separate instances, not interchangeable structures.
5. **Countable recognition criterion:** a *conditional* uniqueness theorem from locally finite closed coverage and all prescribed finite closed extension responses. Make the closure relation an explicit input, then separately instantiate strongness for C0 and strict `d`-closure for CF.

## Dependency / integration graph

```
existing finite predimension + no-cross APIs
    |--> A: C0 finite age --> C0 limit --> C0 Ramsey applications
    |--> B: CF partial level lift --> CF embedding monoid --> CF Ramsey/rational results
    |--> C: CF generic limit identification ------------> CF presentation
    |--> F: orientation and relative degree work
abstract Ramsey-space theorem --> E: each concrete Ellentuck space
D: general Ramsey transfer lemmas (parallel) --> concrete A/B instances
all certified endpoints --> G: marker audit, manuscript edits, PDF
```

**Definition of done for every track:** complete theorem statement in English; matching quantified Lean declaration; no unstated `Allowed`, extension or totalization premise; successful exact build and `#print axioms`; negative/adversarial examples (empty source/target, nonedges, incomplete block, nonclosed base, distinct component orders); status/commit pin in ledger. Internal role-separated review is a pre-merge gate; it is *not* independent human refereeing.

## Editorial simplifications to attempt after the endpoints close

- In `03a_enumeration_C0`, shorten free amalgamation by citing once the common-base component partition and edge-orientation invariance, followed by the **single** all-values/all-steps tagged amalgam theorem. Do not restore the earlier unnecessary common-order alignment.
- In `03b_enumeration_CF`, replace the several interleaved total/partial map citations in the finite-lift proof by a named **partial-source one-level extension lemma**. The induction becomes one paragraph for existence and one for uniqueness.
- Keep the shared predimension/no-cross/minimal-block arguments in `02_preliminaries`. There is no benefit in re-stating them for each class.
- Make the dependence of the finite Ramsey, Devlin and Ellentuck statements on **unique level lifting** explicit in the verification ledger; avoid duplicate historical comments in the displayed proof.
- Preserve the distinction between weak strong closure, strict `d`-closure, enumeration closure and successor-`d)-closure. A single untyped "closure" API would conceal rather than simplify the hypotheses.

## Internal adversarial panel, October 31 pass

- **Predimension/class referee:** verified weak/strict distinctions and the published free-amalgamation hypotheses; no new counterexample to the finite transfer lemmas.
- **Partial-map referee:** produced the `U≠∅, S=V=∅` counterexample to *totalization* (not to the paper theorem); **P0 marker-scope finding**.
- **Function-values referee:** separated full `b`-value surjectivity from induced graph and order preservation; #264 supplies a fresh-block partial theorem only.
- **Countable referee:** checked that finite labelled responses do not, alone, identify the Fraïssé limit; **P1 packaging requirement**.
- **Ramsey/refinement referee:** checked that the Ramsey property of `Age(O_0^*)` is not the expansion property of the published admissible-order class, and that the `C_F` auxiliary block presentation is not the intrinsic orientation reduct.
- **Certification referee:** audited the visible green markers against the total/partial hypotheses and reviewed the placeholder/axiom scripts. No assertion of a third-party independent referee or a new Lean build is made here.

References: `The-big-Hrushovski` sections 02, 03a, 03b, 04, 05, 06, 07, 08, 10; published *Automorphism groups and Ramsey properties of sparse graphs*, §§4.2 and 6.3; Lean files named above.
