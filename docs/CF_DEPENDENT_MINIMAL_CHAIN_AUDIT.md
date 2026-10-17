# Adversarial audit: finite dependent minimal-step lifting

17 October 2026

## Statement

The standard finite d-closed extension property is about
embeddings e defined *only on the finite source A*. The
older abstract minimal-chain theorem represented these by
total maps V→W, which requires a default target vertex
for every source vertex not yet embedded.

The new theorem uses the canonical subtype map
  e: {v:V | v∈A} → W
and an arbitrary invariant Valid(A,e). It assumes a
pointwise-preserving response over every minimal strict
d-closed step A<_d B:

  given e and Valid(A,e),
  find f:B_subtype→W with Valid(B,f)
  and f(v)=e(v) for every old v∈A.

The finite minimal-step decomposition of a≤d c then
iterates this response, yielding an embedding of c which
restricts literally to the prescribed e on a.
There is no requirement that W be inhabited, no
arbitrary extension of e to all of V, and no quotient
identification of source labels.

The abstract theorem is independent of the C_F growth
function and of the countable tagged construction. It
should be reusable in both C_0 and C_F finite extension
and coherent EPPA/Ramsey arguments.

## Six hostile mathematical checks

1. **Actual source names.** A map that merely embeds an
isomorphic copy of A into W is insufficient. The theorem
keeps the domain subtype of *the given* a and enforces
equality on every original vertex at every stage.

2. **No total-map default.** The codomain W may in
principle be empty. The new statement only mentions maps
from finite subtypes which are actually embedded, so
it never manufactures a dummy W-element outside the
current source. This avoids an unnecessary Inhabited W
hypothesis.

3. **Strictness.** The chain contains minimal
IsMinimalDClosedStep inclusions, not weak strongness.
The abstract step hypothesis matches exactly the
decomposition theorem. Intermediate copies must
retain strict closure if that is part of Valid.

4. **Pointwise composition.** For a≤b≤c, the equality
g|_b=f together with f|_a=e implies g|_a=e.
The proof explicitly carries the subset inclusions
and uses proof-irrelevance for the finite subtype
membership witnesses, not a heuristic equality of images.

5. **Finite termination.** The minimal chain is obtained
by finite cardinality induction; there is no countable
fairness assumption and no infinite background work.
The theorem does not assert that the tagged C_F graph
satisfies the local-response hypothesis.

6. **Next instantiation.** To obtain the full C_F
extension property, take Valid(A,e) to encode inducedness
and global strict d-closedness of the actual image.
The remaining interface is the literal one-step
response on arbitrary labelled finite target subsets
(PR #187), followed by this induction. Neither
instantiation nor the total C_F Fraïssé property
is silently certified by the abstract theorem alone.

GREEN validation requires exact compiled declarations,
the standard-axiom report and no-placeholder scan.
The six checks are independent internal hostile
mathematical analyses, not outside referees.

## CI repair and clean-base review (17 October 2026)

The original PR #188 failed during Lean elaboration on the exact message `Unnecessary generalizing argument: Variable e is generalized automatically`, so the clause `induction chain generalizing e with` was replaced by `induction chain with`. This branch starts directly from current `main` to avoid the old PR's merge conflict. Proof status remains pending until the exact integrated CI build, axioms and placeholder checks all succeed.
