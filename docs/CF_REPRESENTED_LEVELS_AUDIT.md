# Adversarial audit: represented and skipped C_F birth levels

1 November 2026. Internal mathematical checks, not external
independent referee reports.

## Statement

`representedLevels s` is the literal finite set of birth
indices among the vertices of a finite source s. A level n is
represented if and only if `selectedRequests s n` is nonempty.
For a finite b-closed source, if n is not represented then

    stageCut s (n+1) = image Sum.inl (stageCut s n).

Thus the induction may leave an unrepresented source cut
unchanged, instead of inserting a spurious new block or forcing
a strictly increasing target map on all ambient construction levels.

## Hostile checks

1. **Empty source:** representedLevels is empty and every
   selectedRequests family is empty, including at n=0.
2. **Complete block property:** a nonempty selected family
   is detected by one actual birth vertex, not a chosen
   named old support. The equality of next-cut images
   separately uses b-closedness to keep whole blocks.
3. **Missing levels:** n may be arbitrarily far between
   represented levels. The theorem imposes no gap on
   target indices and does not construct a total
   increasing map of all `Nat`.
4. **Avoided false extension:** a finite singleton born
   on source level 1 may be sent to level 0. There is
   no strictly increasing map of Nat with h(1)=0;
   the induction must act only on represented levels.
5. **Literal inclusion:** the empty-step equality is
   with `Sum.inl` on the actual source stage carrier,
   not any abstract graph isomorphism.
6. **No false closure:** empty fresh levels add nothing
   to the source cut; strict d-closedness across target
   stage gaps still requires transitivity.
7. **Scope:** the result isolates the source-level
   bookkeeping only; it does not finish existence or
   uniqueness of arbitrary finite level lifts.
8. **Kernel:** three exact axiom endpoints and full CI
   are required before a green manuscript marker.
