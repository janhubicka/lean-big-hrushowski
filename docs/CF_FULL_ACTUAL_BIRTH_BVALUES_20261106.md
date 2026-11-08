# Track B — adversarial audit: one-level complete actual birth b-values

6 November 2026. Independent internal reviewer roles, not outside
human referee reports.

## Main result

On a finite b-closed C_F birth-labelled source s, suppose an old
map e is defined only on its literal selected stage-n source cut.
Its target is any stage U_m and its selected support records are
the actual partial-domain transported requests.

Assume exact preservation of the complete actual birth b-value
for every old source vertex in the selected old cut. This is
spelled out using `cutOldBirthBValue` and the birth-labelled
target image, **not** a generic placeholder predicate.

Then the canonical simultaneous one-level map on the ACTUAL
stage-(n+1) source cut sends the entire finite preimage of each
vertex's complete birth-b-value ONTO the complete finite
preimage of its target birth-b-value in U_(m+1).

The proof identifies the entire target auxiliary b-value,
for both old and fresh target vertices, with the true finite
stage preimage of `birthBValue`. It invokes the already
verified all-vertex one-level functional transport with
the exact old-value induction premise, then uses the literal
`selectedCutEquiv` and source b-value identity.

## Hostile reviewer roles

1. **Actual b-operation:** neither source nor target values
   are invented auxiliary functions. Both are shown exactly
   equal, as finite sets, to preimages of the canonical
   countable `birthBValue`.
2. **Complete values:** all named old support vertices and
   ALL fresh ordinals of each selected block are included;
   an edge-neighbour subset or one fresh representative
   would not suffice for a functional embedding.
3. **Partial source:** e is defined only on the selected
   subtype, not on the complete original source old stage,
   including the empty-target-old-stage case.
4. **Old hypothesis:** preservation of old values is an
   *explicit* induction premise. It is NOT inferred merely
   from induced graph and order. The premise is converted
   with `oldBValue_image_iff_birthBValue`.
5. **Target levels:** m may precede n; no monotone map of
   the entire ambient birth-index set is assumed.
6. **Literal source map:** `selectedCutEquiv` maps
   the complete selected carrier to the actual stage cut
   bijectively. It is not an arbitrary renamed copy.
7. **No false uniqueness:** these lemmas construct a
   function preserving complete b-values under the old
   premise. They do not yet prove an arbitrary functional
   embedding is this function; target request code and
   finite ordinal rigidity remain necessary.
8. **Countable compatibility:** this proves one represented
   level only. Across target gaps the completed image must
   be carried by canonical ascent; the complete birth
   identity `birthBValue_ascend_exact` is in pending
   PR #320. Full represented-level induction remains open.
9. **Kernel:** four exact axiom endpoints are recorded in a
   separate `CheckAxiomsCFTrackBFullBirth.lean`, collected
   by the merged CI workflow. Full build, standard-axiom
   scan, no-placeholder audit and finite regressions are
   required before merging or promoting paper markers.
10. **Manuscript:** no source text or green validation mark
    is changed by this PR. The full finite unique lifting,
    restriction/composition and embedding-monoid statements
    remain partial.

These checks are internal hostile review roles, not claims of
independent external refereeing.

## Integration state (6 November 2026)

The parent literal old/new birth-value bridge was merged into
main by PR #330 (merge commit 7286eb2f74b6c97907d1a28a9ce55778b1c50cbd),
following successful full CI run 42216713837. This PR now
targets main directly and adds only the new exact target and
literal-source all-vertex lifting equalities. All its own
proof obligations require a NEW full CI run on the updated base;
the earlier failing run predated the parent repair and does
not count as evidence for these declarations.
