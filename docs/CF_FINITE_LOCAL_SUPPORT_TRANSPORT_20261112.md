# Track E — finite-source transport of complete supports

## Statement and proof

The existing global-support equation requires an embedding of the
entire countable birth carrier. We now formulate a local version.

Let \(s\) be a finite **b-closed** set of vertices in the actual
\(C_F\) birth structure and let \(e:s\to M\) preserve the complete
auxiliary b-values and the birth-level map \(h\) on \(s\).
Then, for every \(v\in s\),

\[
h[\sigma(v)]=\sigma(e(v)),
\]

where \(\sigma(v)\) denotes the set of birth levels represented in
the **whole least b-generated closure** of \(v\).

Since \(s\) is b-closed, the full generated closure of \(v\) lies
in \(s\). Exact b-value preservation on this set implies exact
transport of the generated closure by the existing certified
`birthGeneratedClosure_image_of_bValues` theorem. Transporting
birth levels on this finite closure gives the displayed equation.
The proof uses a total extension only to evaluate finite-set images:
it neither assumes nor proves that the extension preserves the
graph or auxiliary functions outside \(s\).

A second exact theorem substitutes the *constructed* finite
prescribed lift from Track B, using
`finiteSourceLiftOfCut_birthBValues` and
`finiteSourcePrescribedLift_birthLevel`. It needs strictly
increasing target levels only on the birth levels represented
in \(s\), not a globally increasing map of \(\mathbb N\).

## Adversarial mathematical review (internal roles)

- **Partiality:** the map is defined on the finite subtype only.
  The externally extended function is not an embedding away from
  that subtype; all its required equalities are restricted to
  the generated closure of the chosen source vertex.
- **Closure:** full b-closedness of \(s\) is needed; a subset
  containing only \(v\) and not its generated dependencies
  cannot justify exact support transport.
- **Values:** equality of whole b-values is essential; preserving
  only the immediate adjacency list or one-sided values is not enough.
- **Levels:** the level assignment need only agree on the finite
  source; no arbitrary unrepresented target-level coordinates
  are constrained.
- **Injectivity:** not used in the support-image lemma. It is needed
  for the genuine finite functional embedding proved in Track B,
  but not for the finite-closure calculation itself.
- **Scope:** this is an equality of finite supports, **not**
  the full range equation or finite uniqueness. The reverse
  range inclusion still needs the latter; the actual Ellentuck
  space requires a further countable lift and approximation map.
- **Trust:** two local equations and the instantiated theorem
  are audited by a standalone Lean entrypoint. Standard axiom
  checks, placeholder scan and exact-head build are the gate.
  Internal review roles are not independent human referees.

## Integration status

Keep the manuscript's Section 6 validation markers unchanged.
This intermediate theorem is suitable for the Track B → Track E
interface in the later finite inverse-lift induction.

Expected verification command:

```sh
lake build BigHrushovski.HrushovskiEllentuckFiniteSupportTransport
lake env lean CheckTrackEFiniteSupportTransport.lean
python3 scripts/check_no_placeholders.py
```
