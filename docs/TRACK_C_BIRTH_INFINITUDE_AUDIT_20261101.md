# Track C — countably infinite birth carrier

The manuscript requires the canonical C_F birth graph to be a
countably **infinite** generic. The Lean birth vertex type
`Σ n : ℕ, FreshAt F K n` was proved countable, but that does
not prove it is infinite.

Here `StageRequest` is an actual d-closed support and a complete
bounded ordered local type; its `OrderedLocalType.minimal` proof
forces the fresh size to be positive. The new
`request_has_fresh_vertex` packages this fact, and
`birthVertex_infinite_of_requests` applies the sigma-type
infinite instance once every stage has a request. The exact
`natEquivBirth_nonempty_of_requests` then uses countability
**and** infinitude to produce a natural-number carrier equivalence.

## Hostile internal referee panel

- **Countability referee:** an arbitrary countable type could be
  finite; the fresh-request-per-level hypothesis is indispensable.
- **Request referee:** a request's complete minimal step must
  have positive fresh size; a spurious zero-size code would not
  establish infinitude.
- **Injectivity referee:** distinct birth levels give distinct
  sigma constructors, so no different levels can collapse.
- **Class referee:** the existence of requests remains a separate
  consequence of the paper's one-vertex membership and
  empty-base d-closedness hypotheses. The numerical conditions
  F(0)=0, monotonicity, unboundedness alone do not imply it;
  F(x)=3 max(x,0) is a negative test.
- **Certification referee:** no published statement is marked
  verified until the singleton request and countable
  identification are instantiated, and until exact CI passes.

This is an internal, role-separated adversarial review, not a
panel of external human referees. Source marker promotion is
not requested by this PR.
