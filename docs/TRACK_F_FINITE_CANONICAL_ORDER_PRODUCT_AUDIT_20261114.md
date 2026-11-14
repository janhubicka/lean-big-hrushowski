# Track F — finite canonical labelled order count

14 November 2026. This is stacked on the proposed complete
history-to-canonical-assignment bijection (#543, #547, #551,
#553, #556). None of these new endpoints is declared
Lean-validated until exact-head compilation and axiom checking
succeed. No manuscript or validation-marker edits are made.

## Intended theorem

For a finite orientation A, let \(\mathcal O_{\rm can}(A)\) be the
set of actual labelled strict linear orders satisfying the precise
Lean predicate \`IsFiniteCanonicalComponentEnumeration\`: the
SCCs are intervals, their ordering is successor-first, and the
complete directed adjacency code on every actual
one-component successor closure is lexicographically minimal
with the induced positions of its strict lower part fixed.

Write \(\mathscr B(A)\) for the actual set of strongly connected
components, \(\ell(A)\) for the number of legal consecutive
rankings of these components, and
\(g_A(B)=|\operatorname{Aut}(A[C_B])_{(P_B)}|\) for the
induced pointwise stabilizer of the strict lower part.

The proposed Lean theorem is

\[
 |\mathcal O_{\rm can}(A)|
  = \ell(A)\prod_{B\in\mathscr B(A)}g_A(B).
\]

It is an exact finite count of **labelled** orders, not of
isomorphism classes.

## Mathematical dependence

1. At each fixed legal SCC ranking, complete canonical
   component assignments are the **image** of genuinely
   reachable complete tagged histories, using the two
   previously submitted directions of the bijection.
2. The execution map is injective on those reachable
   histories, using the exact history inverse.
3. The unconditional reachable-history count, already
   Lean-checked and merged in #533, gives the product
   of the local factors in the chronology prescribed by r.
4. The equivalence r between SCCs and a consecutive
   ordinal reindexes the finite product without changing
   its value.
5. The existing, Lean-checked exact canonical-data
   correspondence (#488) sums the rank-specific product
   over the \(\ell(A)\) legal SCC rankings.

No independent count of synthetic records is substituted
for a count of actual orders.

## Adversarial panel — seven mathematical and formal challenge roles

1. **Definition referee.** The theorem counts *exactly* the
   class \`IsFiniteCanonicalComponentEnumeration\`.
   It is NOT evidence that the published paper's expansion
   convention is identical. That identification requires
   a separate line-by-line audit and, if appropriate, a
   formally stated equivalence before manuscript marks move.
2. **Injection referee.** Equality of cardinalities of
   histories and canonical assignments requires the
   history execution map to be injective. Merely knowing
   that every assignment has a history is insufficient.
3. **Reachability referee.** A complete list of tagged SCC
   orders need not be legal. Each new choice must satisfy
   the complete local canonical-code predicate when made.
4. **Dependent-label referee.** The ordered components are
   genuine labelled finite subtypes. The count must not
   divide by any SCC automorphism group a second time.
5. **Reindexing referee.** The local factors may be reordered
   by any legal SCC ranking without affecting the finite
   product. This must use a genuine bijection of finite
   indexing types, not an arbitrary list reordering with
   repetitions or omissions.
6. **Boundary referee.** The empty orientation and the
   possibility of incomparable SCCs must be covered.
   The empty product and the unique empty ranking are not
   exceptional assumptions.
7. **Certification referee.** Exact-head Lean compilation,
   a named theorem-axiom audit, source placeholder scan,
   and independent small finite regressions are required.
   The role-separated panel is not independent external
   human peer review.

## Regression tests

The existing independent test suite exhausts all 653
oriented finite graphs on at most four labelled vertices,
checking the actual global canonical-order set against
rank-specific SCC data; the tagged-history generator
independently obtains the same total of 1,764 canonical
orders and checks the fibre sizes for every legal ranking
and reachable history. These small examples are not
a substitute for the Lean proof over all finite objects.

## Separate Ramsey obligations

Even after a successful kernel check, this is **not**
a complete statement of the infinite big Ramsey degree:
one must identify the exact manuscript's admissible
expansion convention with this finite one, establish
the relevant infinite upper and lower bounds and recurrence
in the original language, and audit any use of the
successor-tree theorem. The \(N_F\) arguments remain
independent. Do not promote a manuscript validation
marker solely on the basis of this finite count.
