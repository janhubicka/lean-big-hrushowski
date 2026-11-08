# Track A: adversarial audit of genuinely growing labelled functional response

Date: 1 November 2026. This is a role-separated internal
mathematical audit; no independent external referees were used.

## Exact theorem

`FiniteCatalogue.exists_growingFiniteOrdinalFunctionalResponse`
takes a finite canonical C₀ stage S on Fin a, a finite canonical
functional extension diagram D, and a prescribed functional
embedding of its source into S. The output is a finite canonical
C₀ stage T on Fin m with **m > a**, two induced strong copies
of S and D.target, exact preservation of all their full unary
values, and pointwise agreement of the source maps. Each old
numerical coordinate is fixed.

## Referee 1 — growth cannot be inferred from the request

A requested extension may contribute no new vertex. The
existing finite ordinal response therefore does not assert
`size>a`. We subsequently apply the separately validated
strict-growth theorem to the *entire responding stage*. If
the first response had size `size`, its injected old map
with `(f x).val=x.val` forces `a≤size`:
otherwise the old vertex named `size` would have to
map to a forbidden target ordinal. The final growth
`size<m` then gives `a<m`.

## Referee 2 — preserving a second factor

The target graph D.target may have a completely
different component chronology on its base. The first
finite response preserves both complete unary values
and both induced graph embeddings. The growth step
preserves the entire responding intermediate unary
operation and graph; composing their images gives
exact full target unary values after growth. This
uses equality, not just an inclusion.

## Referee 3 — fixed old names

Both finite maps preserve the numerical coordinates
of their respective old carriers. Therefore
`(grow (response x)).val = x.val` for every old
vertex, and the required source diagram equality
is preserved by applying the same `grow` map
to both sides.

## Referee 4 — strongness under composition

The finite response gives strong images of S and
D.target inside its intermediate graph. The
growth extension gives a strong copy of that entire
intermediate graph in T. `GraphOn.strong_image_iff`
transports the two first strongness assertions,
and transitivity gives both images strong in T.
Merely composing induced embeddings without these
strongness arguments would be insufficient.

## Referee 5 — proper source hypothesis

The prescribed source map is required to be
injective, graph-induced and to preserve **all**
canonical one-generated unary values. It need
not map component ranks numerically, but its
image is a functional substructure. Strong graph
embeddings without unary closedness do not define
a functional amalgamation request.

## Referee 6 — empty and degenerate cases

If the finite old stage is empty, the initial
response may also be empty. The growth theorem
still contributes a concrete fresh isolated
vertex, giving a proper finite stage. Unused
minimal-component index ranks are permitted;
no new condition on their surjectivity is assumed.

## Referee 7 — remaining limit construction

This theorem solves the finite successor task
for **applicable** functional diagrams.
For an inapplicable scheduled request or no
decoded request, use the growth-only successor.
A coherent finite Nat-stage structure must
still be assembled, preserving graph edges,
nonedges and full unary values across all
successors. A fair schedule and limit theorem
then give the functional extension property.
The countable `C0-free-generic` proposition is
not yet proved unconditionally.

## Certification gate

Exact kernel build of `C0FunctionalGrowingResponse.lean`
and standard-axiom audit of
`CheckC0FunctionalGrowingResponse.lean` with
no-placeholder scan in the dedicated
`track-a-growing-response.yml` workflow.
No green manuscript marker or merge before
those checks succeed.
