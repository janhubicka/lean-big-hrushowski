# Track F — canonical local N₀ fibres (11 November 2026)

Parent: Track F integration PR #270, not main. No manuscript text or validation markers changed.

## Finite theorem, with exact scope

For an actual strongly connected component B, define C_B as its complete directed successor closure, P_B = C_B \ B, and g_A(B) as the pointwise stabilizer of P_B in Aut(A[C_B]), for the **induced orientation** on C_B. With any bijective enumeration of C_B as base, the new canonical class selects the least *complete row-major directed adjacency code* among enumerations agreeing with the base at every position of P_B. The new bridge proves:

- Every member fixes these lower positions pointwise.
- Changing the base by permuting the positions outside P_B leaves the entire canonical class unchanged.
- The class has **exactly g_A(B) members** and is nonempty.
- The construction is indexed by the actual SCC B, not a spurious ambient closure or an arbitrary vertex ordering.

The result follows by applying the existing fixed-lower lex-minimum theorem to the induced closure; it does **not** prove the global bijection between these classes and permitted vertex orders, the factor-product formula *for those orders*, an N₀ Ramsey theorem, or the N_F upper bound.

## Adversarial referee panel

1. **Induced-closure referee:** An incoming leaf to a directed three-cycle makes the global orientation rigid while its cycle closure still has three local automorphisms. The theorem uses the induced orientation on C_B. The finite regression rejects the substitution of the ambient automorphism group.
2. **Pointwise referee:** In the two-sink fork, fixing a lower pair pointwise differs from fixing it only as a set. The formal enumeration agreement is positionwise. The regression checks both stabilizer counts.
3. **Complete-code referee:** The code records *every* ordered vertex pair, including negative entries and arrow direction. The theorem imports the full row-major code, not a mere positive-edge list.
4. **Base-independence referee:** Two bases are allowed to differ in the top component but must place each lower vertex at the **same index**, not merely induce the same underlying set. This is exactly what is proved.
5. **SCC representative referee:** The local factor is constant along each SCC by the existing component-closure and lower-part equality theorems. The new theorem is stated using the actual ComponentObject and componentGenerator solely for typing; it does not identify global and local automorphisms.
6. **Counting referee:** The equality counts canonical *local closure enumerations*. Independence from lower-order history is a cardinality statement, not independence of choice sets. The missing global order bijection and successor-first compatibility are not declared solved.
7. **Certification referee:** Kernel-checked proof plus standard-axiom audit and placeholders are required. A passing Python enumeration alone is not a Lean certificate. No green marker until the exact-head dedicated CI succeeds.

## Independent regression

The Python test exhausts all 653 orientations on at most four vertices with outgoing degree at most two, including the empty orientation. It evaluates 11,067 ordered-lower-part classes and 13,995 base enumerations, comparing the minimum full directed code class to the pointwise induced stabilizer and testing base-independence. It passed locally on 11 November. A dedicated GitHub workflow separately builds the Lean module, prints each exact theorem's axioms, scans for placeholders, and runs this test.

## Next proof boundary

The genuine next target is to construct a finite bijection between global permitted vertex orders and (i) a linear extension of the intrinsic SCC order together with (ii) these locally canonical classes for each component **relative to the already ordered lower part**. The dependent-history counting lemma is available and should be applied only after this bijection is established. The infinite N₀ recurrence and upper-bound Ramsey theorem remain open. N_F has only the finite sink obstruction within Track F.
