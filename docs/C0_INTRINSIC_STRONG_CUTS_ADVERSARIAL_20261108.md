# Track A: adversarial review of intrinsic predecessor cuts

Date: 8 November 2026. Scope: `C0CountableIntrinsicComponents.lean`
on the draft intrinsic-components parent PR. These are **internal,
role-separated checks**, not reports from external referees.

## Exact mathematical statements

For any finite-valued reflexive-transitive unary closure (C) on an
arbitrary carrier (V), let
(P(x)=\{y:C(y)=C(x)\}) and (L(x)=C(x)\setminus P(x)).
The proposed Lean lemmas establish:

1. The *literal finite-set decomposition* (C(x)=P(x)\cup L(x)),
   the disjointness of these two pieces, and (C(x)\setminus L(x)=P(x)).
2. **Full unary closedness** of the finite strict-lower set:
   if (y\in L(x)), then (C(y)\subseteq L(x)).
3. Given a countable graph with cofinal finite canonical C₀ stages
   whose complete unary values agree literally with (C), every
   finite (C)-closed set is **globally strong**. In particular,
   (L(x)) and (C(x)) are finite globally strong sets.

This is not yet the claim that (L(x)\subseteq C(x)) is a *minimal
strong extension*: the difference is the single component (P(x)),
but minimality also requires the certified finite canonical
closed-heredity and closed-base frontloading arguments. No ordered
enumeration, Fraïssé uniqueness, or canonical within-block order
is obtained here.

## Referee A: no extra finiteness hypothesis

All component and lower sets are finite because (C(x)) itself is
a `Finset`, even though (V) may be infinite. The proof never
takes `Fintype V`, chooses a generating point or assumes a
global finite number of components.

## Referee B: proper inclusion, not distinct points

The closure of a different vertex in the **same** component is
equal to (C(x)). The downward-cardinality argument applies only
to vertices in the actual set (L(x)). If (z\in C(y)) and
(y\in L(x)), then the exact transitivity hypothesis gives
(C(z)\subseteq C(y)\subsetneq C(x)).
The resulting strict inequality of finite cardinalities proves
(z\notin P(x)), while transitivity proves (z\in C(x)).

## Referee C: use full closure rather than local neighbours

An earlier source could contain non-neighbour vertices reachable
through several components. Closure of (L(x)) must be under the
*entire* named operation (C). The proof does not replace it by
an immediate-neighbour condition.

## Referee D: correct quantifier in the strongness transfer

For every finite (b\supseteq s), cofinality supplies a finite
canonical stage containing (b). The already certified
`localStrong_of_canonicalFiniteStages` proves (s\leq stage(n))
since the full unary closure of (s) is contained in (s).
Strongness restricts to (s\leq b). We do **not** infer global
strongness merely because (s) lies inside *one* finite strong
stage. The quantified cofinality and stage theorem are essential.

## Referee E: finite computational falsification attempt

The independently extended Python check enumerates **all 66,067**
unary operations with (|V|\leq4), filters the **390**
reflexive-transitive complete ones, and verifies the exact
decomposition, disjointness and closure of (L(x)), as well as
the earlier component/descent properties. This is a diagnostic
counterexample search, not a replacement for kernel checking.

## Referee F: kernel/axiom gates and dependencies

The eight new endpoints are added to
`CheckC0IntrinsicCountable.lean`. The dedicated intrinsic
workflow must compile the exact branch, print their axioms
(no `sorryAx` or new axioms), run the no-placeholder scan and
run the finite regression. Because this branch is stacked on
the unmerged intrinsic-components PR, no merged or manuscript
**GREEN** status is claimed until both branches pass exact CI.

## Remaining gap

Construct the fair enabled-component enumeration of type `omega`,
prove finite closed prefixes and minimal strong single-component
steps using canonical hereditary/frontloading results, recover
exact complete values under the selected order, and complete the
countable functional Fraïssé/ordered-representative analysis.
