# Track F — every actual component-interval order is lex-representable

Stacked on draft #392 (and #387, #353, orientation integration
#270). This is the missing *surjectivity* of the component/local-rank
encoding for genuine labelled orders, not a categorical equivalence.

Given an enumeration e with SCC intervals, rank components by the
position of their first actual vertex. Order the vertices of each
component by their original positions in e. The ordinary lexicographic
comparison of the two numerical coordinates is exactly the original
e-comparison on the **same labelled vertex set**. If the enumeration
is also successor-first, the recovered component ranking is a legal
linear extension of intrinsic reverse reachability.

This complements the already proved component-rank/local-rank
construction and order-comparison uniqueness from #353/#387. It
does not yet impose the fixed local representative choice of manuscript
v52, Section 7.4.4; that is a distinct finite orbit-identification
task. The infinite N0 degree-one theorem and recurrence remain open.

## Six adversarial referee roles

1. **Rank referee:** every genuine SCC has a distinct first position;
   relative ranking is consecutive, not an arbitrary subset of Fin n.
2. **Order referee:** compares labelled vertices exactly, not merely
   isomorphism types or component quotients.
3. **Interval referee:** the component-interval hypothesis is needed;
   interleaving two SCCs would invalidate the reconstruction.
4. **Successor referee:** legal component ranking is obtained only
   when proper successors precede their sources in e.
5. **Local referee:** numerical position ranks are locally injective,
   but no selected ordered closure representative or generator label
   is smuggled into their definition.
6. **Completeness referee:** the full finite permitted-order count
   still needs to identify precisely the chosen local order orbits
   over the already ordered lower part. No infinite Ramsey theorem.

Exact named axioms, placeholder check and an independently written
exhaustive finite verifier are run by an isolated GitHub Actions
workflow; draft status remains until exact-head CI succeeds.
