# Track F — actual SCC lexicographic enumeration (12 November 2026)

Stacked on draft PR #434, itself based on the Track F integration
branch #270 (including merged #413 and #425). No TeX or
validation-marker changes.

## Proof endpoints awaiting exact-head kernel certification

An SCC ranking is a finite bijection from the actual set of SCCs
to a consecutive ordinal. A locally injective rank function
\(a:V\to\mathbb N\) distinguishes vertices inside each SCC.
The existing key \((r([v]),a(v))\) defines a strict lexicographic
order on V.

The new module \`N0RealizeLexEnumeration.lean\` equips V with that
induced finite linear order and uses \`Fintype.orderIsoFinOfCardEq\`
to construct a *genuine* bijective enumeration

\[
e_{r,a}:\operatorname{Fin}(|V|)\simeq V.
\]

Its inherited pairwise comparisons agree literally with the
given lexicographic relation. It proves that:

- every SCC is an interval of \(e_{r,a}\), without requiring
  r to respect the dependencies;
- if r is a legal linear extension, \(e_{r,a}\) is successor-first;
- \(e_{r,a}\) is a member of the actual finite successor-first
  component-interval enumeration family;
- restriction to every finite subset, including the true C_B,
  retains exactly the global lex comparison on that subset;
- conversely every actual SCC-interval enumeration of V has
  the same labelled order relation as such a constructed
  enumeration with component ranking extracted from first
  occurrences and local ranks extracted from actual positions.

## Adversarial referee panel (internal role checks, not human review)

1. **Actual enumeration referee.** A strict order relation alone
   is insufficient. The constructed finite linear order must
   yield a bijection from exactly \(\operatorname{Fin}(|V|)\).
2. **Injectivity referee.** Local rank injectivity must be
   sufficient for the *whole* lexicographic key to be injective,
   even if rank values repeat on different SCCs. The existing
   \`vertexLexKey_injective\` establishes exactly this.
3. **Interval referee.** Lexicographic component rank is the
   primary key, so different SCCs cannot interleave. A
   putative proof using only successor-first would not suffice.
4. **Dependency referee.** A legal SCC ranking makes every
   proper successor component precede its source. The proof
   uses the intrinsic component precedence, not arbitrary
   chronological labels.
5. **Reconstruction referee.** Recovering the relative order
   requires comparisons of all vertex pairs, not only the
   directed edges. The original enumeration and the
   constructed enumeration may have differently named finite
   ordinal index types, so claim equality of *labelled order
   relations*, not ill-typed equality of enumerations.
6. **Local-code referee.** The localRank function is currently
   unrestricted beyond local injectivity. Thus the theorem
   does not claim that every constructed enumeration satisfies
   the canonical adjacency-code condition.
7. **CI referee.** \`#print axioms\` for seven exact endpoints
   and placeholder scan are mandatory; finite regressions
   do not certify Lean proof terms.

The regression enumerates the 653 finite orientations of size
at most four, all legal/illegal component rankings, a substantial
family of injective local ranks, and every actual SCC-interval
enumeration. It tests exact reconstruction and rejects both
noninjective component keys and illegal dependency rankings.

## Remaining proof boundary

We now have both (a) restriction of a global enumeration to all
C_B, and (b) construction of an actual global enumeration from
component ranks and locally injective vertex ranks. The remaining
nontrivial step is to select the local ranks recursively using
the canonical complete-matrix code over the *already ordered*
lower part and prove a bijection between those compatible choices
and globally canonical orders. The \(\ell(A)\prod_Bg_A(B)\)
global expansion count remains outside the proved endpoint
until that compatibility and surjectivity argument is formalized.
