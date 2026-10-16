# Adversarial audit: complete local requests in the countable C_F graph

16 October 2026

## The precise target

Let a finite source A be strictly d-closed in an actual stage U_n,
and let P be a literally named strictly d-closed support in U_n
with P subset A. Let t be an admissible complete ordered minimal
local extension on P plus a nonempty fresh ordered block of
size m <= K(|P|).

The actual request catalogue of U_n includes t over that literal P,
giving a fresh tagged block B_t in U_(n+1). The finite response
theorem, and global strict d-closure of all finite stages,
should imply that the image of A union B_t in the countable
birth-labelled graph is globally strictly d-closed. Moreover
the complete local code t is **induced**, including all nonedges,
in that same countable graph.

The exact endpoints are

* CFCoherentTower.finiteClosedPart_global
* CFCoherentTower.orderedCode_globalResponse

Both are conditional finite-source statements, not genericity.

## Five hostile mathematical checks

**1. Named base and chosen embedding.** The literal support P is an
actual subset of U_n. One cannot replace it with an isomorphic
but differently embedded support: doing so would not extend the
prescribed embedding of A. The request theorem fixes the support
names and keeps the complete graph code over them.

**2. Arbitrary old source.** The local request is based on P, not
on all of A. For the union A + B_t to be closed, we need
P subset A and A <=d U_n. The finite right-factor lemma and
arbitrary-sub-batch theorem jointly prove d-closedness in U_(n+1).
Merely knowing the isolated P + B_t is minimal is insufficient.

**3. Whole countable graph.** It is not enough to be d-closed in
U_(n+1); an unrelated later stage could in principle destroy
closure. The already proposed globally closed stage theorem
provides U_(n+1) <=d V. Strict transitivity promotes the
finite response to global strict d-closedness.

**4. Nonedges and partial functions.** Full inducedness of the
finite local graph is preserved by PR #159's inducedness of
each stage in the birth graph. This does **not** prove that
the future functional language R,H has the right domains and
complete values. That is a distinct theorem, still open.

**5. Completeness and source transport.** The theorem only
handles admissible ordered local code t and a size proof
m <= K(|P|). To deduce the finite extension property of
the countable graph, one must show every abstract minimal
d-closed extension of an already embedded finite source
transports to such an allowed code at some stage. This
requires the canonical local-support theorem, normalization
of the entire graph (including nonedges), and the published
uniform d-closure bound. The finite minimal-chain induction
from PR #154 then supplies arbitrary finite extensions.

## Negative controls

* K=0 may exclude every nonempty minimal extension, so the
  construction cannot be declared generic for arbitrary K.
* If P is not contained in A, the fresh block may have old
  neighbours outside A; the right-factor argument fails.
* If an induced map is replaced by a mere edge-preserving map,
  extra edges in the target can invalidate both the complete
  local code and its predimension.
* Strict d-closedness must not be weakened to self-sufficiency;
  the paper's embedding notion uses strict inequalities.

All five roles are deliberately separate internal hostile
mathematical checks, not separately instantiated referee
agents or an independent human certification. Keep theorems
provisional until final Lean CI, standard-axiom and
no-placeholder audits pass.
