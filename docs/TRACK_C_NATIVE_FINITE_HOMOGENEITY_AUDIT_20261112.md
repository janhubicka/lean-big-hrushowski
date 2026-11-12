# Track C — native-carrier finite strong homogeneity

**Status:** proposed proof in draft PR #458; exact-head Lean kernel build,
axiom audit, and placeholder scan are required before certification.
The following are role-separated *internal* adversarial reviews,
not external human referee reports.

## Statement

For the actual birth-labelled graph of the published `C_F` class,
let `a,b` be finite sets of its original vertices, both globally
strictly `d`-closed. Let `p` be an equivalence between their
literal induced vertex subtypes preserving and reflecting graph
adjacency. Then there exists a bijective automorphism of the
entire **original birth graph** agreeing pointwise with `p`
on all of `a`.

The assumptions on `F` are the published nonnegative domain/codomain,
zero, monotone, unbounded, finite class strictly closed free joins,
strictly closed empty base and singleton membership. No named
external comparison model or target automorphism is assumed.

## Adversarial referee panel

**R1 — Source carrier.** The theorem quantifies over
`a b : Finset (PublishedBirthVertex ...)` and
`p : {v // v ∈ a} ≃ {v // v ∈ b}`; unlike the previous theorem,
no `Nat`-labelled finite source is a hypothesis. The
`Nat ≃ PublishedBirthVertex` needed by the back-and-forth is
constructed internally using the verified standard strong
Fraïssé-limit presentation. Countability alone is insufficient.

**R2 — Partial-isomorphism transport.** The helper
`finitePullbackSubtypeEquiv` is an actual equivalence between the
finite induced subtype and its exact preimage under the
chosen vertex equivalence. Both forward and inverse compute
`ι` and `ι.symm` on literal vertices. It does not replace the
original finite source graph by an arbitrarily numbered copy.

**R3 — Direction of composition.** The Nat partial map is
`A.trans (p.trans B.symm)`, where `A` identifies the source
Nat subtype with its original-vertex subtype and `B`
identifies the corresponding target. Thus
`ι (q.equiv (A.symm x)).val = (p x).val` for each old vertex.
Reversing either `A` or `B` breaks this identity.

**R4 — Strict versus weak closure.** The two native finite sets
must satisfy `IsGloballyDClosed` in the *entire* birth graph.
The transfer uses `globallyDClosed_pullback_iff`, whose reverse
direction requires a genuine vertex equivalence. A merely strong
finite image would not satisfy the strict back-and-forth invariant.

**R5 — Induced graph.** The finite graph hypothesis is `adj ↔ adj`
for **all pairs** from the source. In particular, nonedges are
reflected. The final automorphism is an `Equiv` satisfying the
same iff on all pairs of the countable graph. An injective
homomorphism would not be adequate.

**R6 — Pointwise agreement.** The argument applies the native
automorphism from the previous PR to the exact transported
finite map. The final identity `β x.val = (p x).val`
is established through the source and target subtype equivalences,
not from a bare set equality or existence of an unprescribed
isomorphic copy.

**R7 — Boundary cases.** Both `a` and `b` may be empty. Their
equivalence is then unique, and the empty base is indeed
globally strictly closed under the published class hypotheses.
The proof does not require `a` and `b` to be intervals,
enumeration prefixes, or entire birth levels.

**R8 — Logical dependencies.** The direct birth-limit certificate
was proved in merged PR #420, independently of the comparison
isomorphism. Strong homogeneity on a supplied numbered carrier
was proved in merged PR #437 from the strict joint-step recursion.
The new theorem only transports a finite prescribed map to that
already certified argument; no new infinite back-and-forth
or unproved extension property is postulated.

**R9 — Scope and paper.** This is homogeneity of the graph reduct
for its strict `d`-closed finite embeddings. It is **not** a claim
that the automorphism preserves canonical order, block roots,
the auxiliary `b` function, the final `R,H` functions or
the level structure. It does not certify finite unique level
lifting, the functional embedding monoid, the big Ramsey
theorems, or any Ellentuck-space claim. No manuscript marker
should be upgraded until kernel checking finishes and the
exact statement has been compared.

## Validation gate

A dedicated GitHub workflow builds
`BigHrushovski.CFPublishedNativeHomogeneity`,
checks both exported theorems using `#print axioms` and
performs the repository-wide no-placeholders scan. The full
Lean build on the same current head is required as well.
An isolated source review is not a substitute for those checks.

Negative tests to keep in mind: replacing a carrier equivalence
by a mere injection, using weakly strong rather than strictly
closed finite images, or dropping reflection of nonedges all
destroy hypotheses needed by the conclusion. These are logical
boundary checks rather than proof of new converse claims.
