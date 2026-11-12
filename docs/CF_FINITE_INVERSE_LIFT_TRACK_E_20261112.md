# Track E: actual finite inverse level lifts — 12 November 2026

## Mathematical contribution

Let $s$ be a finite, b-closed vertex set in the countable
$C_F$ birth presentation, and let $h:\mathbb N\to\mathbb N$
be strictly increasing. Suppose the birth level of **every**
vertex of $s$ belongs to the range of $h$.

There is a genuine induced, ordered functional embedding
$g:s\to M_F$ in the complete auxiliary b-language such that

$$
  h(\pi(g(v)))=\pi(v)\qquad(v\in s).
$$

The map preserves and reflects edges and nonedges, the canonical
birth order and birth-level preorder, and transports every
complete b-value onto the target value. A second theorem
chooses the same finite prescribed lift in the actual (R,H)
language: it transports every R(v), every defined H(S), and
reflects the partial H-domain.

**This is the inverse finite-lift *existence* requirement, not
finite *uniqueness*.** In particular the theorem does not
construct a global self-embedding or assert the full
copy-range equation.

The input range condition is precisely the one automatically
available when the entire finite generated closure of a
vertex has its birth levels in the range of $h$:
for $s=\Gamma(v)$, every vertex of $s$ has a birth
level belonging to that complete support.

The theorem `birthSingletonClosure_inverseRHLift_exists` now applies
this observation directly to one vertex: from
`v ∈ birthLevelDomain F K (Set.range h)` and strict monotonicity
of `h`, it constructs the same ordered partial (R,H) lift on
the **entire least finite b-generated closure** of `v`.
All vertices in this closure have birth levels belonging to
`birthLevelSupport F K v`. The original finite range hypothesis
therefore follows from complete support membership, without any
additional assumption about closure vertices.

## Reason for the finite partial inverse

Define `chosenInverseLevel h q` by choosing one preimage of
$q$ when $q\in\mathrm{range}$h$$, and using 0 otherwise.
The choice is unconstrained outside the range.

Since $h$ is strictly increasing, the chosen inverse is
strictly increasing on the finite set of levels represented
in $s$. This supplies exactly the predicate
`StrictOnRepresented`, used by the previously certified
finite prescribed-lift theorem.

The finite lifting proof therefore does not require a
globally strictly increasing inverse on all natural numbers.
Such a map may not exist if a represented source level is
positive but its required target level is 0.

## Independent adversarial mathematical reviews (internal roles)

1. **Range condition.** It applies to all represented birth
   levels, not only the source vertex's own birth level.
   Otherwise a dependency vertex might have no inverse level.
2. **Partial inverse.** Values at unrepresented levels are
   irrelevant. No global monotonicity of the chosen inverse
   is asserted.
3. **Order.** Strict monotonicity of h is necessary to
   reflect the order of distinct represented source levels.
   Mere injectivity of h does not suffice.
4. **Finite source.** The source may be empty and may have
   unrepresented gaps; the existing finite lift treats both.
5. **Exact language.** The b-valued finite lift and the
   R/H-valued finite lift use the *same constructed* map
   and the already certified closed-source equivalence.
   The domain of partial H is reflected, not ignored.
6. **Range and uniqueness.** Existence of inverse lifts does
   not imply equality with restrictions of a given countable
   embedding. That inference requires finite uniqueness.
7. **Trust.** Internal mathematical review is not an
   independent human referee. Exact compilation,
   `#print axioms` checks and placeholder scanning
   are required before any validation marker is promoted.

## Next obligation

Prove finite uniqueness of arbitrary genuine (R,H) embeddings
with prescribed levels, using comparison of complete ordered
local request matrices. Then the abstract finite range
criterion can combine this inverse-lift existence with the
already certified forward range inclusion. Countable
existence and the actual approximation code remain separate.

No manuscript validation markers have been changed.
