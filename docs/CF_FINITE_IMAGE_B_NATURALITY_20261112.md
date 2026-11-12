# Track B: finite images and complete b-value composition

12 November 2026. This independent module prepares the
composition-compatibility clause of finite unique C_F
level lifting. It does not assume the first map is the
canonical prescribed lift, or is defined outside its finite
source; the second map is likewise genuinely partial.

## Exact mathematical content

For a finite source s and a map e from its selected subtype
into the actual birth carrier, suppose e carries each
finite-source complete b-value ONTO the complete ambient
target b-value. Then the literal finite set e[s] is b-closed.
The induced map s→e[s] carries complete finite-source b-values
exactly onto the finite-source b-values inside e[s].
Consequently, if g:e[s]→M_F^† is another such complete-b
preserving partial map, the composite g∘e preserves complete
b-values on s.

## Six independent adversarial referee roles

1. **No missing domain vertices:** Every source value
   `finiteSourceBirthBValue s x` is a finite subset
   of the genuine source subtype and is therefore contained
   in its univ. This makes e[b_s(x)] a subset of e[s].
   Equality with b(e(x)) forces image b-closedness; a
   one-sided inclusion would not suffice.
2. **Literal image, not arbitrary closure:** The target
   finite set is exactly the image of the univ of the
   original source subtype under e. We do not replace it
   with a d-closed hull or an abstract isomorphic copy.
3. **No unjustified injectivity:** Image b-closedness and
   b-value naturality do not need injectivity; the proof
   uses only the injective forgetful map of the target
   subtype to recover equality of finite sets.
   Future *embedding* composition will assume injectivity
   and induced graph preservation independently.
4. **Both function values complete:** Naturalness is an
   equality of complete finite-source values inside e[s].
   Composition uses it to transport EVERY vertex of the
   b-value, not only support neighbours, block roots or
   cardinalities.
5. **Partial source/target discipline:** The first map
   e is defined only on s. The second map g is defined
   only on e[s]. Both are evaluated solely on their
   explicitly certified domain vertices. There is no
   extension to the countable universe or the whole
   finite old stage.
6. **Remaining work and proof trust:** This module is
   the unary-value portion of finite composition
   compatibility. Inducedness/injectivity/order/level
   transport must still be assembled and the resulting
   map compared to the canonical unique lift. The
   countable monoid remains open. Require exact-head
   Lean, standard-axiom, placeholder and regression
   gates before any manuscript marker is changed.

These are role-separated internal adversarial checks,
not external human referee reports.

```sh
lake build BigHrushovski.CFFiniteClosedImageNaturality
lake env lean CheckAxiomsCFTrackBFiniteImageNaturality.lean
python3 scripts/check_no_placeholders.py
```
