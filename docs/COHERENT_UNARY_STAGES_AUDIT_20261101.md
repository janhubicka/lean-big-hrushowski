# Reusable countable limit of coherent finite unary operations

Date: 1 November 2026. This is a role-separated adversarial
self-audit, not independent human or external-agent refereeing.

## Exact hypotheses and conclusion

A finite stage at time n is the consecutive interval
`[0,size n)`. We have a finite set-valued function
`value n x : Finset ℕ`. We require:

- Strictly increasing stage sizes.
- For x in stage n, `value n x` is wholly in that stage.
- For x already in stage n, its full value at n+1 is
  **equal** to its complete value at n.

No graph, predimension or countable model is assumed.
The limit operation is obtained by choosing one stage
containing x and taking its finite value. The theorem
`limitValue_eq_stage` proves that this choice is
independent and equals the value of x at every other
stage containing it. Each stage is therefore closed
under the complete limit operation, and every finite
set has a finite closed stage containing it.

## Adversarial referee 1 — fixed finite-valued functions

The conclusion is about exact equality of `Finset ℕ`
unary values, not only eventual membership of the
generator or monotone inclusion. Without equality,
new vertices may enter the old unary value and the
old stage need not be a functional substructure.
This invalidates the finite-age Fraïssé argument.

## Adversarial referee 2 — gaps in labels

Pointwise growth of finite sets with arbitrary gaps
does not cover ℕ. Stage domains are explicitly
`Finset.range (size n)`. Strict growth gives
`n ≤ size n` by the existing `NatStageCoverage`
lemma, so every natural vertex eventually enters.
No separately assumed exhaustion is hidden here.

## Adversarial referee 3 — coherence beyond successors

The successor equality must be iterated through
arbitrary later stages. The proof obtains size
monotonicity from strict growth, then proves
`value_stable n m` by induction on m. This
is used both when the chosen witness stage is
earlier and when it is later than a specified stage.

## Adversarial referee 4 — complete generated substructures

Because each value is a `Finset`, the union
operation is finitely valued on every vertex.
For any finite s, finite stage coverage provides
n with s⊆range(size n). Exact stability and
finite support imply that range(size n) is
closed under the *limit* operation. This
proves finite closed covers without assuming
finite closure as an additional input.

## Adversarial referee 5 — no circular genericity

The construction does not presuppose the existence
of a functional Fraïssé limit, model-theoretic
algebraic closure, or the strong graph extension
property. Its only hypotheses are elementary
coherent finite stage data. It is reusable in
other finite-valued unary expansions, including
those where a minimal-component presentation
is not given.

## Adversarial referee 6 — remaining C₀ obligations

One must still construct a strictly growing
finite functional stage successor which responds
to every applicable scheduled request.
The finite response and forced growth are
handled in independent Track A branches.
The countable recursion must check graph
inducedness, finite strong-step preservation,
fairness and the closure-value equality.
This module provides the unary operation
and its exact persistence/closed-cover
interface only. The full countable
`C0-free-generic` proposition remains partial.

## Certification gate

Dedicated workflow `coherent-unary-stages.yml`
builds `CoherentNatUnaryStages.lean` and
audits its eight exact `#print axioms`
endpoints, with the standard no-placeholder
scan. No manuscript marker is promoted without
these checks.
