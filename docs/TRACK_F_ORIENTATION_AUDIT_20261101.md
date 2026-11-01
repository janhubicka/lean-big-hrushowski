# Track F — orientation and relative big Ramsey degrees: adversarial audit

Date: 1 November 2026. Source baseline: Lean main 1f5fcd06fe6fcdbfdfeab997125b31609df98b38; manuscript main tree 264bc23505f2c6c9fda83b544edf55badcd120b2 (v52). Scope from Track A plan in PR #266.

This track owns only its new Orientation*, N0ExactDegrees*, NFSinkObstruction* proof files and dedicated audit checks. Neither the paper nor shared C0/CF sources are modified here.

## Exact statements and status

| Statement | Paper | Lean status |
|---|---|---|
| Successor-closed finite sets stable under union and intersection; sink pairs have no directed edges | Sections 7–8 | New finite lemmas in OrientationRelativeFinite.lean, CI pending |
| Uniqueness of common predecessor of two sinks under four-cycle exclusion | Lemma NF-sink-pairs (partial) | New finite lemma, CI pending |
| Exact formula BRD(A,N0)=ell(A) times product of g_A(B) | Theorem N0-exact | Open; finite diagnostic only |
| Recurrence and degree one for permitted ordered successor-closed structures | Lemma N0-order-degree-one | Open |
| The sink graph of NF is Rado in every strong self-copy | Lemma NF-sink-Rado | Open |
| The complete successor-d-closure formula for sink pairs | Lemma NF-sink-pairs | Open beyond elementary finite uniqueness |
| Unbounded root-arity for all r>=3 | Lemma NF-unbounded-root-arity | Open; r=3,4 checked exhaustively |
| Two sink trace types but four unavoidable embedding colours | Proposition NF-trace-not-optimal | Open |
| Upper bound for NF | No claim | Explicitly open in paper; not in Track F |

Do not promote any infinite theorem to Lean-verified on the basis of these finite checks.

## Role-separated internal adversarial review

1. **Orientation and edge-count referee.** Arrows are stored at the tail, and the underlying graph counts unordered edges. A later theorem that successor-closed sets are strong must explicitly use the outdegree bound and predimension identity. It is not in this PR.
2. **Sink pair referee.** The proof of uniqueness of a common predecessor uses the absence of four-cycles. The hypothesis is explicit in the new Lean theorem. Without it, two different common predecessors are possible.
3. **Strong-versus-strict referee.** The fork x→a,b witnesses that the successor-closed pair {a,b} is strong but not strictly d-closed: both the pair and the full fork have predimension 4. This is the obstruction underlying the sink graph definition.
4. **Local symmetries referee.** A directed 3-cycle with one incoming leaf has a trivial automorphism group but the finite degree formula gives three; with one outgoing leaf it gives one. Whole-structure automorphism groups must not be substituted for the pointwise-lower-part component automorphism groups.
5. **Higher-root referee.** The r=3 gadget has pairwise closed sinks but their triple is not d-closed. This is why the Rado sink graph alone does not determine successor-d-closed embeddings, and arbitrary Rado subcopies cannot simply be lifted to NF.
6. **Coordinate-host referee.** Distinct pointed closure coordinates in the paper's W may have the same integer coordinate. The comparison by coordinate is NOT a global linear order; only permitted finite closed parts are ordered and preserved by the return map. The infinite formalization must capture that weaker exact assertion.
7. **Certification referee.** The new finite Python checker imports no paper checker. No kernel-checked infinite recurrence, coordinate host, Rado extension, canonical colouring or big Ramsey degree theorem is claimed.

These are independent mathematical attack roles within one audit, not a panel of external human referees.

## Remaining exact interfaces

- OrientationRelativeStrong.lean: prove that successor-closed implies strong; formalize the relative extension lemma and reflected induced embeddings.
- N0ExactDegreesFinite.lean: define finite successor closure, SCC decomposition, lower parts, local canonical orders and count all permitted orders, including empty A.
- N0ExactDegreesInfinite.lean: construct the strong orientation generic, prove recurrence and degree-one Ramsey via locally ordered coordinate host, then prove exact formula.
- NFSinkObstructionFinite.lean: strict d-closure, root-set description, growth threshold q, star extension, and the cycle gadget for every r>=3.
- NFSinkObstructionInfinite.lean: strong generic, sink graph Rado and absoluteness in strong copies, unavoidable nonedge two-colouring, trace count and four-colour obstruction.

Acceptance gate: exact manuscript statement matched by fully quantified Lean theorem, passing CI and standard-axiom audit, no placeholders, explicit finite negative cases and an independent adversarial review. The existing C0 enumeration closure, successor closure, and strict successor-d-closure must remain distinct.

## 1 November finite extension

New module `OrientationRelativeStrong.lean` proves the concrete implication `IsSuccessorClosed s → GraphOn.IsStrong s t` for all finite `s⊆t`, by bounding new unoriented edges by the outgoing edges whose tail lies outside `s`. It also proves the exact numerical bound on newly occurring edges. The proof does **not** assume the target predimension is nonnegative and does **not** confuse weak strongness with strict `d`-closure. The new finite API also proves there is no edge between the exclusive parts of two successor-closed vertex sets. All these new Lean endpoints remain **CI pending** until the branch build and `CheckOrientationAxioms.lean` audit both succeed.

An independent exhaustive checker tests 21,195 comparisons across 653 admissible orientations on at most four vertices. A regular tournament on five vertices (underlying K5) shows that the strongness conclusion fails if successor-closedness is omitted: the singleton `{0}` has predimension 2 and the whole K5 has predimension 0. These finite diagnostics are not an infinite Ramsey theorem.

**Further adversarial checks:** the new edge-tail argument counts undirected edges once despite an orientation; it does not require an acyclic orientation; source and target can be empty; internal strongly connected components cause no problem because only edges crossing the closed base matter. The `N_0` recurrence, the `N_F` Rado sink graph, and all degree assertions remain open in Lean.

## Finite directed reachability and SCC API (1 November 2026)

New `OrientationReachability.lean` defines reflexive/transitive arrow reachability; mutual reachability; the **least** finite successor-closed hull of any vertex set; its monotonicity and idempotence; strongness of every generated hull by the preceding edge-tail lemma; and equality of SCC fibres exactly for mutually reachable vertices. No artificial acyclicity hypothesis is used. This is the structural beginning of the `N_0` exact-degree track, **not** a proof of the finite component-order count or the infinite Ramsey theorem.

Independent exhaustive checks over every orientation of up to four vertices examined **10,167** generated successor closures, **21,411** minimality comparisons against closed supersets, and **10,192** vertex-pair SCC equality tests. The numerical diagnostic does not certify the Lean theorem. Lean kernel compilation/axioms are still subject to passing Actions on this branch.

The SCC calculation is separate from `C0` enumeration blocks. It uses actual directed paths rather than simply naming a `C0` minimal increment a strongly connected component. That identification is a separate orientation-extension theorem.

## Minimal successor-closed increments (1 November, further validation)

New `OrientationMinimalStep.lean` states the genuine minimal proper successor-closed extension predicate. Using the least successor closure of a new vertex, it proves every fresh vertex reaches every other fresh vertex; hence `t \ s = component x` for **each** fresh generator `x`. This isolates the SCC decomposition fact in the manuscript's `N_0` proof without importing an unproved order-count or infinite genericity result.

The independent exhaustive checker found **3,761** minimal successor-closed steps across all **653** orientations up to four vertices and checked **4,203** generator-to-component identifications. Two isolated sinks show why *minimality* is necessary. Passing finite tests are not Lean certification; all new theorems remain pending branch CI.

## Component dependency partial order (1 November 2026)

`OrientationComponentOrder.lean` now isolates the **strict** relation
`ComponentPrecedes B C`: a proper directed path from component `C`
to component `B`. It proves irreflexivity, transitivity, asymmetry and
independence of the representatives in each SCC. A directed path
either stays inside one SCC or gives the strict comparison of two
distinct components. These facts are purely finite and separate the
intrinsic dependency relation from an arbitrary chronological order.

The independent Python regression enumerates **30,887**
2-orientations on up to five vertices, checks the component relation
and compares the number of its linear extensions computed by
permutations with an independent recurrence over downsets.
The result is a finite diagnostic, not a proof of the manuscript's
`N_0` degree-one Ramsey theorem.

**Referee counterchecks:** directed cycles must be *collapsed*
into a single SCC before forming the component order; otherwise
the proposed order is cyclic. A nonreachable pair of components
must remain incomparable; a time order of a chosen enumeration is
not a graph invariant. The zero-vertex orientation has one empty
linear extension. The definitions state these distinctions explicitly.
The Lean results remain CI-pending until the exact branch build passes.

## Successor-closed sets as component downsets

The new `OrientationComponentDownsets.lean` proves precisely:
a finite vertex set is successor-closed if and only if it contains
the **whole** strongly connected component of each of its vertices
and is downward closed under the intrinsic strict component
dependency relation. It also separates the two forward
implications into reusable lemmata. This makes the component
decomposition and its allowable orders explicit rather than
using an arbitrary chronological presentation.

An independent test checked the equivalence on all **977,655**
vertex subsets of the **30,887** orientations on up to five
vertices. The complementary independent test checks direct
permitted-vertex-order counts against
`ell(A) * product_B |Aut(C_B)_(P_B)|` on all 653 orientations of
at most four vertices and 1,312 sampled orientations of five
vertices (1,965 orientations; 172,514 orders considered). It
does not use the manuscript's original counting script.

**Scope boundary:** the finite counting formula itself is
still not an elaborated Lean theorem; we have only the SCC
dependency/downset infrastructure and independent arithmetic
regressions. The degree-one Ramsey theorem and recurrence of
the ordered generic remain entirely open in Lean. No
validation marker in the paper is promoted by these checks.

## Local component symmetry factor (1 November)

New `N0LocalSymmetry.lean` defines the complete oriented-graph
automorphisms of a finite one-component successor closure `C_B`
which fix its lower successor part `P_B` pointwise. It proves
that the identity belongs to this finite set, distinct local
automorphisms transport a fixed enumeration to distinct
enumerations, the orbit has exactly the stabilizer's cardinality,
and each transport fixes every old point. These are the
kernel-level counting interfaces for the local factor `g_A(B)`.

**Adversarial limit:** this currently counts **enumerations**.
Identifying their transported finite linear orders, proving that
these are precisely all locally permitted orders, assembling
independent choices along component linear extensions, and
proving recurrence and infinite Ramsey degree one remain open.
Do not cite this lemma alone as a verification of
`thm:N0-exact`. CI/axiom audit required at the new commit.
