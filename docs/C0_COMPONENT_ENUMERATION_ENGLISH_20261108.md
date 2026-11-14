# Countable \(C_0\) closure-component enumeration — proof and verification

Updated 13 November 2026. This is an English proof guide, not an additional Lean
certificate. It concerns the **unordered complete-unary functional presentation**
and the chronology of its intrinsic closure-components. The uniform local orders
required by the manuscript's Ramsey expansion are a separate step.

## Proposition

Let \(N\) be the graph reduct of the constructed countable functional \(C_0\)
limit, with complete finite unary values \(C(x)\). There is an enumeration of
\(N\) by consecutive finite components such that every component appears after
all its strict lower components, each nonempty component increment is minimal
strong, each finite component prefix is globally strong, and the induced
complete unary values coincide with \(C\). The sequence of components, and
hence the resulting vertex enumeration, has order type \(\omega\).

### 1. Intrinsic components

Put
\[
P(x)=\{y:C(y)=C(x)\},\qquad L(x)=C(x)\setminus P(x).
\]
The nonempty finite sets \(P(x)\) partition the vertices and are the component
fibres in every finite canonical presentation. If \(y\in L(x)\), then
\(C(y)\subsetneq C(x)\); in particular \(|C(y)|<|C(x)|\) and the entire
component \(P(y)\) lies in \(L(x)\). Thus every component has finitely many
strict lower components, and the lower-component relation has no cycles.
These facts are formalized in \`C0CountableIntrinsicComponents.lean\`, using
the finite equality-of-closures theorem.

### 2. A fair enumeration of components

Give a component \(P\) the distinct numerical priority \(\min P\). At each
stage list the *eligible* unlisted component of least priority, where
eligibility means that all strict lower components have been listed.

An eligible component always exists: choose an unlisted component with
smallest \(|C(x)|\). An unlisted strict lower component would have smaller
closure size, contrary to the choice. Every component is eventually listed:
induct on its closure size to see that its finitely many lower components
are listed; once eligible, it can be delayed only by components of smaller
numerical priority, of which there are finitely many. Components never
repeat. Since the vertex set is infinite and every component is finite,
there are infinitely many stages.

**Why not sort by closure size?** There may be infinitely many components
of minimal closure size. Sorting globally by size can therefore starve
components of larger size; the eligible least-priority rule does not.

The fair prefixes and their exhaustion are Lean-certified (#412); exact
component births and cofinal canonical finite presentations were subsequently
certified (#417, #433). Componentwise injective numberings give consecutive
finite intervals and a vertex order of type \(\omega\) (#439, #457).

### 3. Strong and minimal component cuts

Let \(Q\) be the union of previously listed components and \(P\) the next.
Both \(Q\) and \(Z=Q\cup P\) are finite and \(C\)-closed, because every strict
lower component of each of their vertices has already appeared.

Choose a finite canonical stage containing \(Z\). Closed heredity gives
a canonical minimal-component presentation of \(Z\) with exactly the
inherited complete unary values; its intrinsic component fibres are the
\(P(x)\). Frontload the closed set \(Q\) in this finite presentation.
Only one nonempty component, \(P\), remains. Consequently \(Q\leq Z\)
is a minimal strong extension. The finite closed-set theorem also makes
\(Z\) globally strong in \(N\). Neither conclusion follows merely from
the abstract set-valued closure algebra.

The finite one-component interval lemma (#385) and its countable transfer
(#394) certify the minimal-step argument. The fair prefixes and their
strongness are covered by #412 and the subsequent canonical-stage results.

### 4. Preservation of the full unary operation

For every vertex \(x\), the prefix ending at \(P(x)\) contains all of
\(C(x)\). By finite closed heredity its canonical unary value at \(x\)
is *equal* to this full value, not merely contained in it. The exact
birth-index identity is certified in #419, #422 and #427.

The component chronology therefore preserves the original complete
functional structure. The order chosen *within* a component is irrelevant
to this statement, but not to the ordered Ramsey expansion: that expansion
requires the same selected representative of each ordered one-generated
closure type over its already ordered lower part. Sorting each component
by its natural-number labels does not establish this requirement.

### 5. Functional limit: what is already certified

The actual countable functional-stage extension property and its graph
reduct's identification with \(M_0\) are certified in #375. The
arbitrary-\(C\)-closed-base extension property (#459) uses the finite
two-sided functional amalgam and preserves both complete unary values.
The countable functional back-and-forth and closed functional homogeneity
are certified in #512. The direct corollary for *arbitrary* finite closed
functional isomorphisms has since merged in #522, eliminating the need
to carry a separate global-strongness hypothesis in that statement.

The empty-base finite functional universality corollary was
subsequently certified and merged in #511, with its dedicated
exact-head and repository-wide Lean builds passing. None of these unordered results chooses the uniform local
ordered representatives, and none alone proves the paper's ordered
Ramsey or big Ramsey assertions.

## Internal adversarial checks

- **Components:** the equality \(C(x)=C(y)\) identifies entire finite
  component fibres, not single preferred generators.
- **Fairness:** the minimum closure size proves that a component is
  eligible; the minimum numerical priority proves eventual selection.
  Interchanging these arguments would be invalid.
- **Minimality:** closed heredity and frontloading are needed to obtain
  minimal strong increments; closure monotonicity alone is insufficient.
- **Complete functions:** every use of an embedding requires equality
  of the entire named unary value, including every reachable component.
- **Order:** a componentwise \(\omega\)-enumeration is weaker than the
  uniform representative convention of the ordered expansion.
- **Trust:** only statements with merged exact-head kernel and axiom
  audits are called certified; the present prose is not itself formal
  verification.

This replaces duplicate historical status narratives with the proof's
four logical steps and records the current gap without promoting any
manuscript validation marker.
