# Adversarial audit: noncollision of actual partial C_F request tags

30 October 2026

## Scope

The new proof handles a prescribed map defined only on the selected
finite old source S. It proves that two distinct literal source
request records cannot acquire the same target request tag. No
extension of the map to the whole source old stage is chosen.

The result combines the already-verified target request
construction and full adjacency-code equality with a new generic
lemma: under an injective map e:S→V, equality of the *literal*
support images e[P] and e[Q] reflects equality P=Q.

## Hostile mathematical checks

1. **Empty-target case.** The support-image lemma and the tag
   argument are valid for S=∅ and V=∅, regardless of the
   cardinality of the ambient source old stage U. The proof
   never invokes Nonempty V or a total U→V function.

2. **Named support.** Equality of target supports must recover
   equality of actual source support *sets*, not just their
   cardinalities or isomorphism types. The subtype restriction
   of e is injective by strict monotonicity, and the image
   membership proof reflects support equality vertex by vertex.

3. **Dependent request records.** A source StageRequest includes a
   literal support, an ordered fresh-size index and a complete
   local graph. Equal source supports are combined with equality
   of fresh sizes and the entire row-major adjacency matrix,
   including nonedges. The existing complete-key injectivity
   theorem then identifies the full dependent request records;
   proof certificates are proposition-valued.

4. **Whole-batch injection.** The source old map is injective,
   different source tags are sent to different target tags,
   and each fresh block's canonical Fin cast is injective.
   These three ingredients imply injectivity of one simultaneous
   map sending all selected source blocks to the SAME target
   level, even when the target old stage is empty.

5. **Limits.** This is not yet proof of inducedness, inherited
   stage order or complete b-value preservation for the genuinely
   partial simultaneous map. Nor does it complete induction
   through represented levels. Its new axiom endpoints and full
   CI must pass before certification.

These are separate adversarial mathematical checks within the
project, not reviews by independent external human referees.
