# Track F — injectivity of reachable tagged history execution

14 November 2026. Stacked on PRs #543, #547, #551 and #553.
This is an internal, role-separated adversarial audit, not
independent external human refereeing. No manuscript or
validation-marker changes.

## Exact proposed finite statements

For a legal ranking r and a reachable tagged history h of length n,
execute h by applying the internal SCC-order updates in
chronological order, beginning with the fixed default assignment.

The theorem \`taggedPrefix_of_reachableHistory\` proves that if
one then reads the actual internal orders of the first n
SCCs back from the executed assignment, in ranking order
and newest first, one obtains *exactly h*.

The proof uses:
- The actual next-choice membership theorem, which forces
  the tag at stage n to name precisely \(r^{-1}(n)\).
- \`withComponentOrder_other\`: updating that SCC does not
  overwrite any earlier chosen component.
- \`taggedPrefixFromAssignment_eq_of_agree\`: only the first n
  component orders determine the first n tags.
- The previously certified labelled update and complete
  enumeration reconstruction results, with no quotient by
  isomorphism or graph automorphisms.

In particular, if two *reachable complete* histories execute to
the same family of labelled SCC orders, they are identical.

Combining this proposed injectivity with PR #551 (reachable
histories give canonical assignments) and PR #553
(every canonical assignment gives a reachable history)
gives an exact bijection between the two finite sets,
subject to successful Lean certification of the entire stack.

## Seven adversarial referee checks

1. **Repeated-update referee.** Reverse chronology matters,
   and generic histories may repeat a component; no
   unconditional injectivity is claimed for arbitrary lists.
   Reachability enforces the distinct rank sequence.
2. **Dependent-tag referee.** Equal numbers of vertices do
   not identify different actual SCCs. The tag stores its
   component as part of the dependent pair.
3. **Rank referee.** Every new tag at prefix length n must
   name exactly the component of rank n. This follows
   from membership in the genuine next-choice set, not
   an assertion about any arbitrary list.
4. **Earlier-prefix referee.** An update of the next
   component cannot change any component order already
   chosen, and prefix equality uses only these earlier
   components, not the default orders at later ranks.
5. **Labelled-order referee.** Equality of complete executed
   assignments is literal equality of functions on the
   original SCC carriers, not equality of order isomorphism
   types or adjacency-code classes.
6. **Boundary referee.** The empty orientation and its
   unique empty history are included. The induction also
   admits zero-choice intermediate fibres and remains
   vacuous after a history set becomes empty.
7. **Certification referee.** Exact-head Lean compilation,
   named theorem-axiom audit, placeholder scan and
   independent exhaustive finite tests must pass.
   The finite test is not a proof for arbitrarily large A.

## Independent finite checks

For all orientations on at most four labelled vertices,
every legal SCC ranking, and every reachable canonical
tagged history, the script verifies that its executed
assignment contains exactly the chronological component
orders of that history, with no collisions among complete
reachable histories. It also verifies persistence of the
chosen orders at every prefix. The expected total is 1,764
complete canonical histories over all 653 test orientations.

## Next integration

After certification of this PR and its upstream stack,
the exact finite history/assignment bijection can be stated
as a cardinality identity. The already merged unconditional
reachable-history product theorem (#533) then gives the
rank-specific product; the already merged canonical data
identity (#488) sums over legal rankings.

A separate elementary reindexing of the product along the
finite component ranking may be needed to present it as
\(\ell(A)\prod_B g_A(B)\). More importantly, a referee must
compare the finite canonical-order predicate with the
paper's admissible expansion definition before any
manuscript marker is promoted. The infinite N₀ big
Ramsey degree theorem remains outside this finite argument.
