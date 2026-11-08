# Track A: adversarial audit of the finite one-component step

Date: 8 November 2026. Code:
`BigHrushovski/C0OneRemainingComponent.lean`.
The referee roles below are independent **internal mathematical checks**,
not additional human referee reports.

## Exact theorem

Let (G) be a finite graph and `κ : V → Fin n` a canonical
component presentation in which every nonempty index step is
*minimal strong* (empty index slots are permitted). Let (S\subseteq
V) be closed under the **complete** canonical unary operation.
If (V\setminus S) is *exactly* the single component containing
some (x\in V), then

`G.toPredimension.IsMinimalStrongStep S Finset.univ`.

No countable genericity, linear order of unrelated components, or
distinguished generator is assumed.

## Referee A: cut location

The original component index `j=(κ x).val` need not be the first
nonempty slot. The frontloaded indexing is `frontloadIndex κ S`.
Every earlier original vertex lies in S: if it did not, the
complement hypothesis would put it in the component of x, forcing
its index to be j, contradicting strict earlierness. Thus the
frontloaded cut at `n+j` is exactly S.

## Referee B: no later vertices are lost

Every vertex not in S lies in the component at j. Thus it appears
by frontloaded cut `n+j+1`; every member of S was frontloaded
before n. This is literal equality with the full finite vertex
set, not a cofinality or cardinality argument.

## Referee C: empty versus minimal

The existing certified `frontloadIndex_minimal_steps` gives a
disjunction: the selected step is empty or minimal strong. The
step cannot be empty, because the original vertex x of that
component lies outside S. Therefore the other disjunct is the
required minimal strong step. The proof does not infer minimality
from strongness alone.

## Referee D: closedness and hereditary hypotheses

The theorem explicitly demands exact closedness under
`canonicalValue G κ`. Replacing it by closure under immediate
old neighbours, or allowing the complement to contain only a
*proper subset* of one component, invalidates the call to
frontloading. These are not silently weakened.

## Referee E: empty carrier / empty index slots

The theorem has a witnessing point x, so the empty-vertex case
is vacuous. The finite index may have empty slots; the previous
step-disjunction theorem handles them. The calculation selects
the actual component index of x, not the first nonempty slot.

## Referee F: formal proof gates

The dedicated `track-a-one-component-minimal.yml` workflow builds
the new file, invokes `#print axioms` on the exact endpoint and
runs the no-placeholder scan. This PR is not to be merged until
those checks and the repository Lean check pass. The theorem is
new and **proposed** until exact CI confirms compilation.

## Interface to countable component enumeration

Apply this theorem to the finite induced graph on a closed
set (Z=Q\cup P), where Q is an earlier closed prefix and P
is its single next intrinsic component. Exact finite closed
heredity is needed to present this induced graph canonically;
the equality (Z\setminus Q=P) then supplies the complement
hypothesis. Global strongness of Z is separately established
by the cofinal finite-stage theorem.

Nothing here certifies a fair enumeration of components, the
functional Fraïssé limit, or a canonical order within components.
