# Adversarial audit: finite restricted induced hull transport

22 October 2026

## Mathematical claim

For graphs G on U and H on V, a finite set b⊆U, and a map
f:U→V which is *injective and induced only on b*, the complete
finite strict d-closed hull on b satisfies

  f[cl^d_b(s)] = cl^d_{f[b]}(f[s])   for every s⊆b.

Neither inducedness nor injectivity of f outside b is assumed.
This is a reusable structural theorem for both C_0 and C_F.

## Referee checks

1. **No hidden global injection.** Only injectivity among members of b is stated. The proof constructs an injective total map on the actual finite subtype {u//u∈b}, where the hypothesis is sufficient.
2. **Complete inducedness.** Both edges and nonedges are reflected between vertices in b. This is needed for predimension, unlike a homomorphism.
3. **Exact source vertices.** The finite subtype contains the literal elements of b with membership proofs, not an arbitrary finite enumerated replacement.
4. **Two existing verified maps.** The same finite induced graph on the subtype maps to G by the inclusion and to H by f. The previously checked dClosedHull_image applies to both.
5. **No image omission.** The image of the entire finite subtype is exactly b; the image of its restricted generator set is exactly s, and their f-images are exactly f[b],f[s].
6. **No ambient closure assumption.** b itself need not be globally d-closed; the assertion is about finite hulls computed inside b and its image, not the infinite countable graph.
7. **No support conditions.** The lemma uses no growth function, enumeration, block tags, orientations, or partial H-domain. These remain application-specific hypotheses.
8. **Source-substructure bridge.** If a partial embedding is defined on a closed source X, restricting it to any finite b⊆X supplies these exact hypotheses. The final C_F functional equivalence still needs exact preservation of function-value domains and container closure.
9. **No phantom predimension.** All hulls and predimension calculations concern finite vertex sets.
10. **Formalization boundary.** Three exact theorem endpoints have axiom checks. Do not mark the lemma verified before full CI including placeholder/regression checks.

These are independent internal adversarial proof roles, not external human referees.
