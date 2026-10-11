# Algebraic closure and strong closure in the 2-sparse generic

**Verification checkpoint, 11 October 2026.** This note expands the
algebraic-closure remark in `The-big-Hrushovski/sections/02_preliminaries.tex`
into distinct finite and model-theoretic assertions. It is not a
claim that `acl=cl_s` has already been completely formalized.

## 1. Strict predimension at the finite closure

Let `M₀` be the countable strong Fraïssé generic and let `X` be
finite. Write `C=cl_s(X)`; this is finite and globally strong.
Every proper intermediate set `D` with `X⊆D⊊C` satisfies

`δ(D)>δ(C)`.

To see this, choose among the finite subsets `Y` with
`X⊆Y⊆C` one of minimum predimension. Every
`Z` with `Y⊆Z⊆C` is another candidate, so `Y≤C`.
Since `C≤M₀`, transitivity gives `Y≤M₀`; hence
minimality of the strong closure gives `Y=C`.
Thus `δ(C)` is minimum on `[X,C]`.
If a proper `D` attained that same minimum, it would itself
be strong in `C`, hence globally strong, contradicting
minimality of `C`.

The **leastness** of `C` is essential. For example, in the
edgeless two-vertex graph, the entire graph is strong but not
the least strong set containing its first vertex; taking that
vertex for `D` gives `δ(D)=2<4=δ(C)`.

This is the purpose of the Lean statements
`exists_min_delta_strong`,
`strict_delta_of_least_global` and
`genericStrongClosure_strict_delta`.

## 2. Copies of the finite induced diagram cannot leave C

Suppose `f:C→M₀` is an induced injection fixing `X`.
Put `C'=f[C]`. Preservation and reflection of adjacency imply
`|C'|=|C|` and `δ(C')=δ(C)`, while `X⊆C'`.

If `C⊄C'`, then `D=C∩C'` is a proper intermediate
subset containing `X`, so the strict inequality of Section 1
gives `δ(C∩C')>δ(C)`. Submodularity and `C≤M₀` give

```
δ(C) ≤ δ(C∪C') ≤ δ(C)+δ(C')−δ(C∩C') < δ(C),
```

a contradiction. Hence `C⊆C'`, and equality of cardinality
gives `C=C'`.

This does **not** assert `f=id_C`: the finite structure on
`C` may have automorphisms over `X`. The essential conclusion
is that its induced diagram over `X` cannot be realized using
vertices outside `C`.

The Lean candidate `genericStrongClosure_induced_copy_image`
formalizes precisely this finite combinatorial conclusion.
A first-order existential formula describing the full finite
induced diagram of `C` over `X` has only finitely many possible
realizations, all drawn from `C`. Its coordinate formulas
therefore witness `C⊆acl(X)`. The translation of this
finite diagram into first-order formulas remains to be formalized.

The competing copy `C'` is **not** required to be strong.
Assuming its strength would make the argument circular.

## 3. Strong copies outside a finite forbidden container

Let `C≤M₀` be finite and let `D` be a finite strong
extension of `C`. For every finite `F⊆M₀`, choose a finite
globally strong `B` containing `C∪F`.

Take the free strong amalgam of `B` and `D` over `C`.
Strong free amalgamation gives a finite two-sparse graph in
which the two factors are induced and strong, and their images
meet exactly on `C`. By the extension property of `M₀`,
embed this amalgam globally strongly into `M₀` while fixing
the literal copy of `B` pointwise. The induced image of
`D` is globally strong, agrees with the original embedding
on `C`, and has no new vertex in `F`.

This is the intended content of `exists_disjoint_strong_copy`
and `generic_exists_strong_copy_avoiding`. These candidate
lemmas must be Lean-audited before use.

## 4. Infinitely many conjugates and the converse

Fix `a∉C` and put `D=cl_s(C∪{a})`, which is finite
and globally strong. Section 3 gives, for every finite
forbidden `F`, an induced strong copy of `D` over `C`
sending `a` outside `F`.

Both the original `D` and its copy are globally strong.
Strong homogeneity of `M₀` extends their induced isomorphism
over `C` to an automorphism of `M₀` fixing `C`
pointwise. Consequently the pointwise stabilizer of `C`
has an infinite orbit on `a`.

If `a` were algebraic over `X⊆C`, some first-order
formula with parameters from `X` would have a finite
solution set `F` containing `a`. Every automorphism fixing
`X` pointwise preserves `F`, contradicting the previous
paragraph. Thus `acl(X)⊆cl_s(X)`.

The prospective Lean endpoints are
`generic_strong_automorphism_avoids`,
`generic_outside_closure_infinite_orbit` and
`generic_invariant_finite_subset_strongClosure`.
The finite-copy construction and automorphism consequences
are currently under Lean review.

## 5. Validation boundaries

The following are separate proof obligations and must not be
conflated:

1. Strict predimension at the least finite strong closure.
2. Uniqueness of the **image set** of an induced finite closure
   diagram over the generators.
3. A strong induced copy over the base avoiding **any** finite
   forbidden set, without assuming the forbidden set is strong.
4. A genuine automorphism fixing the base pointwise and moving a
   specified vertex outside the forbidden set.
5. First-order syntax and semantics of induced finite diagrams
   and algebraic formulas, producing the literal `acl` relation.

The first four have explicit proposed Lean modules and independent
finite regression for the first two. The fifth remains to be
formalized. The distinct mathematical and computational checks
in this review were conducted by the same assistant, not by an
externally spawned panel of independent referees.

## Suggested shortening of the manuscript remark

The paragraph justifying strict predimension can be made shorter:
“Choose a subset of `C` containing `X` of minimum
predimension. It is strong in `C`, hence strong in `M₀`,
and therefore equals `C`. Equality of predimension for a
proper intermediate set would make that set strong as well.”

This avoids the extra phrase “inclusion-minimal
predimension-minimising superset”, without weakening the
statement. Apply it as an editorial revision only after the
finite Lean theorem has passed its axiom audit.
