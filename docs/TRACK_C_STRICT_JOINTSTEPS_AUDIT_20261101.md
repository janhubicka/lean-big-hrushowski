# Track C — exact finite strict d-closed joint steps

Branch based on core PR #276; this is a **dependent** proof branch,
not an independent replacement for #276. Its own PR must remain
draft until #276 and this branch both pass the isolated Lean audits.

## Mathematical statement

For two countable graphs M,N on ℕ and an identical real-valued
cardinality growth function F, assume:

- every finite subset of M,N satisfies F(|S|)≤δ(S);
- every finite subset of M,N is contained in a globally **strictly**
  d-closed finite subgraph;
- every finite induced strict d-closed interval a≤_d b in the finite
  growth class admits an induced global strict d-closed response over
  any given induced, globally d-closed copy of its base in M,N;
- ∅ is globally strictly d-closed in both graphs.

Then the graphs are induced-isomorphic.

The proof first extends an arbitrary *strict* finite partial
isomorphism across an arbitrary source vertex (using a finite
strict container), then across a target vertex, retaining all old
values. The existing coherent-union theorem from PR #276 finally
produces a bijection preserving adjacency and nonadjacency.

## Role-separated adversarial review (internal)

- **Class referee:** a graph outside the finite growth class cannot
  be supplied as the source of an extension. The finite container's
  induced graph remains in C_F by the global growth hypothesis.
- **Closure referee:** IsGloballyDClosed is never silently replaced
  by IsGloballyStrong. Weakening strictness would invalidate the
  finite response hypothesis, so only the *forgetful union interface*
  of PR #276 uses the strong structure.
- **Boundary referee:** all finite maps are induced, not merely
  homomorphisms. In particular, old--fresh nonedges and proper
  boundary nonedges are reflected.
- **Map referee:** source/target covers, injectivity and exact old
  image preservation are checked before inversion. The back step
  is obtained by reversing the actual equivalence, not by
  renaming or relabelling source vertices.
- **Empty referee:** no initial map exists without both empty
  closures. These hypotheses remain explicit and cannot be
  inferred merely from finite closed covers.
- **Certification referee:** only exact Lean theorem endpoints
  and a successful isolated CI/axiom audit permit promotion. A
  conditional uniqueness theorem does NOT identify the specific
  birth graph with the printed M_F until its hypotheses are
  instantiated without additions.

Potential negative tests: growth excluded singleton; weakly strong
but not strictly closed old copy; improper nonedge reflection;
source/target carrier not ℕ before a countable-equivalence bridge.

## Still necessary to identify M_F

1. Derive `HasFiniteDClosedIntervalResponses` on ℕ from
   `CFRealFiniteGenericity.finiteRealDClosedInterval_globalResponse`.
   This uses finite-subtype reindexing and a countable carrier bijection.
2. Prove the canonical birth carrier infinite using the one-vertex
   request plus the published empty-base assumption, and choose a
   bijection with ℕ preserving the induced graph.
3. Apply the same finite-cover and extension inputs to the published
   C_F Fraisse limit (or characterize M_F with these exact hypotheses).
4. Connect the actual nonnegative-domain growth F via Track C PR #277.

Status at creation: **proposed Lean proof, isolated CI pending**.
