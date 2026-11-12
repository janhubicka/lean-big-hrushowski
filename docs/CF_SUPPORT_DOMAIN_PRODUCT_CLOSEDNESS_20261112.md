# Track E — closed complete-support-domain codes (12 November 2026)

## Exact statement

Let \(V\) be a vertex set, \(L\) a set of levels, and assign a
**finite** support \(\sigma(v)\subseteq L\) to each vertex \(v\).
For \(S\subseteq L\), put

\[
U[S]=\{v\in V:\sigma(v)\subseteq S\}.
\]

Identify a set \(X\subseteq V\) with its Boolean characteristic
function. The family \(\{U[S]:S\subseteq L\}\) is closed in the
product of discrete two-point spaces \(2^V\).

The proof builds on PR #414. Define
\(\operatorname{cl}(X)=U[\bigcup_{v\in X}\sigma(v)]\).
This is an extensive, monotone, idempotent operation and its fixed points
are exactly the sets \(U[S]\). If \(\operatorname{cl}(X)\ne X\),
choose \(v\in\operatorname{cl}(X)\setminus X\).
Because \(\sigma(v)\) is finite, finitely many vertices of \(X\)
already account for every level in \(\sigma(v)\). Any set agreeing
with \(X\) on those vertices and at \(v\) cannot be complete-support
saturated. This finite Boolean cylinder is an open neighbourhood of
\(X\) disjoint from the family of all \(U[S]\).

No compactness theorem or assumption that \(V\) or \(L\) is
finite enters the proof.

## Concrete instance

Apply the general theorem to the **actual countable** \(C_F\)
birth-labelled carrier with \(\sigma(v)\) the full finite
support of the complete b-generated closure of \(v\).
The result is closedness of the family of these supported
vertex domains, not closedness of the sequences of finite
approximations of functional self-embeddings.

The theorem does **not** prove that every \(U[S]\) is the range
of an \((R,H)\)-embedding or that an arbitrary increasing assignment
of birth levels lifts uniquely. Those are separate Track B
and later Track E obligations.

## Internal adversarial referee checks

1. **Finiteness:** each \(\sigma(v)\) must be finite. The vertex
   carrier and \(X\) can be infinite; no global finite bound on
   supports is required.
2. **Local obstruction:** the finite witness set is chosen *after*
   discovering a missing vertex of \(\operatorname{cl}(X)\).
   Its choice is independent of the competing supported domain.
3. **Empty supports:** vertices with empty support belong to every
   \(U[S]\). They are handled by the same formula, including the
   empty finite witness set.
4. **False union shortcut:** binary unions of complete-support
   domains need not be supported domains. The completion is formed
   from the **union of all support levels** first.
5. **Topology:** the product is \(2^V\), with **discrete Bool** in
   each coordinate; closedness is proved by a basic finite cylinder.
   The space of level sets \(2^L\) is not silently substituted.
6. **Functional copy boundary:** closedness of domains is not the
   required Tychonoff closedness of approximation codes, because
   the latter also contains finite functional labels and first-n
   represented-level approximations.
7. **Trust:** a separate Lean module, exact `#print axioms`
   declarations, placeholder scan, and full CI are required
   before marking this extension certified.

The finite regression checks 8,778 support systems, 102,674
completion/fixed-point assertions and 62,607 excluded
non-domain characteristic codes. These tests are diagnostics,
not a replacement for kernel verification.

## Progress boundary

Track B has now established the existence of prescribed finite
\((R,H)\) lifts (merged PR #416). Finite *uniqueness* of arbitrary
functional embeddings, the countable lifting theorem, and
identification of the copy-range space are still required
before using this result in the proof of the abstract
Ellentuck theorem for the paper's spaces.

The manuscript and its green validation markers are unchanged.
