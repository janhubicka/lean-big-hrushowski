# Track C — final published-domain C_F strong Fraïssé-limit identification

This dependent PR composes three independently isolated or pending
components: the exact published singleton class assumptions (#360),
the arbitrary-carrier published birth-graph theorem (#362) and the
native-carrier Fraïssé limit presentation (#365).

## Exact hypotheses and conclusion

The growth function has the exact manuscript type
`F : ℝ≥0 → ℝ≥0`, is monotone and unbounded with F(0)=0;
the independent finite class assumptions are strict d-closed free
amalgamation, strict d-closedness of the empty substructure in
every finite C_F member, and membership of the one-vertex graph,
numerically F(1)≤2.

The actual comparison structure `M_F : GraphOn V` is *not*
provided with an isomorphism to the birth graph. It is provided
only with the natural strong Fraïssé limit conditions:
countably infinite enumeration, complete finite C_F age,
a covering finite strictly d-closed chain and the full induced,
prescribed finite strict extension property.

The proof derives the three-property finite strict-genericity
characterization from those data. It then obtains an induced
equivalence of the original canonical birth carrier with V,
reflecting all edges and all nonedges.

## Role-separated internal adversarial panel

**Analytic referee.** Continuity is not used in these discrete
predimension calculations and is not introduced as an extra
Lean hypothesis. The canonical extension of F to negative reals
agrees *exactly* at all finite cardinalities; it does not
create additional permitted finite graphs.

**Finite-class referee.** Free amalgamation and empty-base
d-closedness are independent standing assumptions, not
consequences of monotonicity. The singleton F(1)≤2 hypothesis
is exactly age membership of the one-vertex graph.

**Closure referee.** A covering strict d-closed chain yields
finite *globally* strictly d-closed covers; the proof does not
weaken this to ordinary strongness. The empty-base condition
for the comparison graph is derived from the finite class
assumption, not postulated as an extra genericity axiom.

**Extension referee.** The target extension property is induced
(including nonedges) and fixes a literally prescribed old
strong copy. The source may be represented by finite subsets
of a graph on ℕ, but only membership of the *finite endpoint*
in C_F is required. Compare to the manuscript's equivalent
strong extension property for any finite `A ≤_d B`.
A separate proof of this encoding equivalence would be
appropriate before promoting the *named* M_F declaration to green.

**Carrier referee.** Neither `M_F` nor the birth graph is
assumed to be on ℕ. The given ℕ≃V is genuine infinite
countability data, not a claimed graph equivalence. The
conclusion is an actual induced graph isomorphism.

**Non-circularity referee.** None of the four native Fraïssé
limit fields refers to the birth graph or to the desired map.
The only use of graph isomorphism is in the proved conclusion.

**Certification referee.** Exact kernel build and
`#print axioms` for the new final theorem are mandatory;
all dependent PRs must be integrated before the manuscript
lemma is marked fully verified.

Status: new theorem awaiting independent CI, and upstream
integration pending. This is internal role-separated
adversarial checking, not external human refereeing.
