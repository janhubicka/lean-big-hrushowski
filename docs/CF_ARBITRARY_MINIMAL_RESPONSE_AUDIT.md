# Adversarial audit: respond to an arbitrary minimal strict C_F extension

16 October 2026

## The assembled mathematical theorem

Input: a finite complete graph H with old carrier S and a new block B;
the entire old part is a *proper minimal strictly d-closed* subset of
H, and H satisfies the exact growth inequalities defining C_F.
A prescribed injective induced source map f:S→U_n has a strictly
d-closed image in an actual tagged finite stage.

The finite canonical-support theorem extracts the literal subset
P⊆S which is the least strict d-closed hull of all old neighbours
of B. It shows P≤d S, no old neighbour of B lies outside P,
the local extension P<_d P∪B is minimal, and P is its own exact
old-neighbour d-closed hull.

The complete split-local-graph certificate then gives:
(a) exact C_F growth membership for all induced local subsets;
(b) minimal strict local d-closedness;
(c) exact local old-neighbour support.
The graph-theoretic minimal growth-size bound gives the fresh
block estimate |B|≤K(|f[P]|), provided the numerical inverse
domination property is supplied.

The already certified namedLocalExtension_globalResponse theorem
then constructs an induced embedding of the entire graph
S⊕Fin(|B|) into the countable birth-labelled tagged graph,
fixing the prescribed source pointwise and with globally
strictly d-closed finite image. The source, support and fresh
block are not replaced by unrelated isomorphic copies.

Thus the one-step graph-level extension property is reduced
to the standing numerical inverse property and class
membership, without assuming any pre-normalized local code.
The full countable Fraïssé extension property still needs
the finite decomposition/induction over arbitrary extensions
and transport from an arbitrary finite graph carrier to this
old/fresh split presentation.

## Six separately adversarial mathematical checks

1. **No circular response assumption.** The proof uses
only the actual finite tagged stage catalogue, exact local
code transport and globally closed one-block response. It
does not assume the genericity property of the target M.

2. **Nonempty fresh block.** Minimality means the full old
part is strictly smaller than the complete extension.
If B were empty, old vertices would be all vertices.
The proof extracts a genuine fresh b and uses it only for
the numerical every-generator size bound; no such witness
is assumed without proof.

3. **Canonical rather than arbitrary support.** P is
defined as the least strict d-closed hull of the entire
old-neighbour set. Both strict minimality of P<_d P∪B and
the exact support hull are proved; simply choosing any
closed support containing all old neighbours is insufficient
to identify the correct named request.

4. **C_F and numerical hypotheses.** The whole finite
extension H is assumed in the actual growth class.
Its local induced split graph remains in C_F, and the
explicit inverse domination F(m)≤2(k+1)⇒m≤K(k)
bounds the entire local interval. No weak 2-sparsity
or arbitrary bounded K can substitute.

5. **Old image and boundary nonedges.** The old map f
is prescribed and induced; its image is strictly d-closed
in U_n. The local response's old support is exactly
f[P], and the complete boundary equivalence reflects
all absent old-fresh edges outside f[P]. The target map
fixes the old birth labels pointwise.

6. **Global strict closure versus finite copy.** The
selected tagged block is attached among potentially
many simultaneous requests. The exact selected-sub-batch
strict closure and global finite stage closure must both
be applied. The result is globally strictly d-closed,
not merely an induced copy inside the one-block prefix.

## Final interface to be addressed

Any finite strict d-closed extension A≤d C admits a finite
chain of minimal steps. Each step's induced graph may be
presented as a complete old/fresh split graph over the
current source. The already verified minimal-chain lifting
theorem will compose such responses pointwise once the
representation of each step and the codomain map record
are connected. The real growth-to-integer inverse is already
available separately (PR #174).

The six checks above are internal adversarial mathematical
reviews, not independent external human referee agents.
GREEN is allowed only after final integrated Lean compilation,
standard-axiom verification and placeholder scans at the
merged revision.
