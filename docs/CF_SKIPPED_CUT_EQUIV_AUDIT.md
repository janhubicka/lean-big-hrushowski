# Track B: adversarial review of skipped-source-level equivalence

1 November 2026. Internal independent reasoning roles.

If a finite b-closed C_F source has no birth vertex at source
level n, its next cut is literally the Sum.inl image of its
old cut. This inclusion is a bijection of the respective
subtype carriers. The canonical equivalence preserves every
vertex name (up to the literal old inclusion), and preserves
and reflects graph edges and nonedges.

Hostile checks:

- The proof uses **unrepresented** source levels, not merely
  absence of blocks with a particular named old support.
- b-closedness is retained; otherwise a stage cut might omit
  some vertices of a met fresh block.
- The source cut may be empty and its ambient source stage
  nonempty. No target inhabitant or total old-stage map is chosen.
- The equivalence is literally Sum.inl, not a new arbitrary
  numbering. It composes with the canonical `ascend` maps.
- All graph nonedges are reflected because each old-stage
  inclusion is induced.
- The theorem does not assert that a target stage has no
  new vertices; it does not change any target assignment.
- Three exact axiom endpoints and full Lean CI are required
  before marking the result verified.
- The full induction must still combine the skipped-level
  persistence step with the selected-block step at
  represented source levels. Uniqueness of arbitrary
  embeddings remains separate.

These are internal audit roles, not outside referee reports.

Additional checks (2 November 2026):

- **Birth-label referee:** `skippedCutEquiv_birthVertex` proves
  exactly `toVertex (n+1) (skippedCutEquiv u) = toVertex n u`.
  Thus complete auxiliary birth b-values have the same literal
  source vertex argument across skipped levels; this is not
  merely equality up to graph isomorphism.
- **Order referee:** `skippedCutEquiv_stageOrder_iff` proves
  exact preservation **and reflection** of the recursively
  inherited finite-stage order by the skipped-level map.
  It uses the previously verified old-stage order inheritance.
- Both new theorems are listed in the axiom audit. The full CI
  must pass before they count as verified.
