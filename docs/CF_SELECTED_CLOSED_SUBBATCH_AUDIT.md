# Adversarial audit: arbitrary supported selected-block substructures

16 October 2026

## Exact finite statement

Let U be the complete old vertex set in an actual tagged C_F level,
let A be any finite subset with A <=d U, and let D be any finite set of
request tags. Suppose that every selected request r in D has its
literal support P_r contained in A. Put B_D = union of the fresh
vertices tagged by D. Then

    A union B_D <=d U union B_D <=d U',

where U' contains *all* the fresh request blocks of that level.

This is a finite graph-predimension theorem and does not assert
that the countable functional presentation is already constructed.

## Four separate adversarial checks

**Support / no-cross referee.** Every edge between B_D and U must
meet the actual named P_r of the relevant selected request. Since
P_r is contained in A, there is no cross edge between B_D and U\A.
A merely isomorphic but differently embedded support would be
insufficient. Different fresh tags never collide.

**Right-factor referee.** Since A <=d U, the strict no-cross
right-factor theorem applies to the free join of U and A union
B_D over A. It gives A union B_D <=d U union B_D. This
does *not* require each individual fresh block to be d-closed
over A: its designated old support may be a proper subset of A.

**Arbitrary-prefix referee.** U union B_D is not necessarily a
chronological prefix. PR #151, whose integrated Lean workflow
passed, proves that the tagged prefix for an arbitrary set of
request tags D is d-closed in the *entire* level U'. Transitivity
therefore completes the statement. The calculation handles
arbitrary intermediate sets meeting several omitted blocks.

**Necessity / scope referee.** The condition P_r subset A
cannot simply be dropped. For the predimension delta=2|V|-|E|,
take old U={u}, A=empty, and B={x,y,z}, with edges
ux, uy, uz, xy, yz. The extension U <=d U union B is
minimal: every nonempty subset of B gives delta 3 or 4,
strictly above delta(U)=2, while every proper intermediate
has a further extension with non-increasing predimension.
But B alone has delta(B)=4, and adjoining u lowers it to 3.
Hence B is **not** d-closed in U union B. This is a small
predimension control, not a claim that this four-vertex graph
belongs to the particular growth-restricted C_F.

## Simplification for the manuscript

The proof of the finite-block closure lemma need not attach all
selected blocks one by one. Once the old portion A is d-closed,
the complete selected family is a single free factor, and the
already proved arbitrary-prefix theorem supplies the final
closure. This separates the two uses of free amalgamation and
avoids a second induction over the same request tags.

The existing regression for actual tagged batches covers
arbitrary noninitial subsets of request tags. The new Lean
theorem and its axiom print are required to pass the integrated
workflow and placeholder scan before any manuscript marker
is promoted to green.

These four passes are internal adversarial checks, not
independent outside referees.
