# Track E: literal first-n image-level approximations

14 November 2026.

Let \(f\) be a map of the actual countable \(C_F\)
birth carrier, and suppose its birth-level action is
a strictly increasing map \(h:\omega\to\omega\).

Write \(U_n\) for the **literal** stage containing
exactly vertices born before level \(n\). Then

\[
f[U_n]
=
\{v\in \operatorname{range}(f):
  \pi(v)\in h[\{0,\ldots,n-1\}]\}.
\]

This holds without any assumption about the b-value or
R/H operations. It uses only the equation
\(\pi(f(v))=h(\pi(v))\), strict increase of \(h\),
and the exact stage-membership criterion
\(v\in U_n\iff\pi(v)<n\).

If every birth level has an empty-support request,
a vertex occurs at every source level. Consequently
the birth levels represented in \(f[U_n]\) are
**exactly** \(h[\{0,\ldots,n-1\}]\), while the
levels represented in all of \(\operatorname{range}(f)\)
are exactly \(\operatorname{range}(h)\).

These are the literal first-n image-level diagrams
required for the \(\omega\)-level copy-space
identification. The theorem does not yet prove
that the space of these diagrams satisfies A.1–A.4
or that its Tychonoff approximation-code image is closed.

## Independent adversarial mathematical roles

1. **Literal source.** The finite structure is the actual
   \(U_n\), not an abstract isomorphic copy or an arbitrary
   induced subgraph. Its membership is exactly birth level
   less than \(n\).
2. **Correct source cutoff.** The last included source
   level is \(n-1\), not \(n\). This also covers \(U_0\).
3. **No hidden surjectivity.** The right side is the
   intersection of a finite image-level condition with
   \(\operatorname{range}(f)\). It is not the set of
   *all* ambient vertices on those levels.
4. **Strictness, not mere monotonicity.** The reverse
   inclusion uses injectivity of \(h\) to recover the
   source birth level from the target birth level.
5. **Full finite blocks.** The stage \(U_n\) contains
   whole actual birth blocks and their dependencies;
   we do not select single representative vertices.
6. **Realized level sets.** To assert that all values
   \(h(k)\), \(k<n\), actually occur in the image,
   we use a separate vertex-witness hypothesis.
   Without it, an empty source level could be
   spuriously counted as represented.
7. **Topology.** Equality of these finite domains
   identifies the intended approximations but is
   not, on its own, the abstract Ellentuck theorem.
8. **Trust.** These are separate internal mathematical
   challenges, not external human referee reports.
   Exact-head Lean compilation, three named axiom
   inspections, and the placeholder scan are required.

The manuscript and Section 6 validation markers are unchanged.
