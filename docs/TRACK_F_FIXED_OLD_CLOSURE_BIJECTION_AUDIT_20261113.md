# Track F — the complete fixed-old closure-order bijection (13 November 2026)

Stacked on Track F PR #506, itself stacked on #504.
No TeX or validation-marker changes.

## The exact statement

Fix a legal ranking r of the actual strongly connected components,
a complete family \(\mathbf e\) of internal component enumerations,
and one component B. Let x be its chosen generator, let C=C_B be
its complete directed successor closure and P=P_B=C\B.

Write \(e_0\) for the complete enumeration of C inherited from
the assembled global order. For any labelled internal enumeration
\(t:\mathrm{Fin}(|B|)\simeq B\), write \(e_t\) for the enumeration
inherited on C after changing only the order of B to t.

Previous PRs prove that every e_t fixes all the old P-positions
of e_0, and that restricting e_t back to B recovers exactly t.

The new module \`N0StageFixedOldClosureBijection.lean\` proves
the converse: for *any* complete enumeration f of C fixing these
old positions, let t be the order which f induces on the actual
labelled B. Then **e_t=f**.

The proof splits all comparisons in C into the old P part, the
top component B and the cross pairs. Inherited top orders agree
by definition and the top-order restriction theorem (#506).
Old positions agree by hypothesis and #504. All old vertices
precede B in both complete local enumerations by legality and
the old-position preservation theorem. The finite theorem
that a total labelled order determines its enumeration finishes
the proof.

Consequently the **entire** fixed-old enumeration family
is exactly the image of the genuine top-order update map:

\[
 \{f:\mathrm{Fin}(|C|)\simeq C:
       \operatorname{SameLowerPositions}(P,e_0,f)\}
 =
 \{e_t:t:\mathrm{Fin}(|B|)\simeq B\}.
\]

The map is injective by #506. There is no quotient by
automorphisms, and no assumption of canonicality in this
geometric bijection.

## Internal adversarial referee panel

1. **Fixed positions.** Equality of the *relative order* on P
   is not enough without the lower initial-segment hypothesis.
   The proof uses literal old-position agreement from #504.
2. **All vertices present.** Every f is a complete bijection
   on exactly C; neither a partial enumeration nor an
   injection with gaps qualifies.
3. **No other components added.** The new order is extracted
   from B as its original labelled vertex subtype, with
   B contained in C. Unrelated SCCs do not enter.
4. **Three comparison cases.** Old-old follows from fixed
   positions, new-new from the extracted top order, and
   old-new from P being initial in the induced order on C.
5. **Injectivity.** Restriction of the assembled e_t back
   to B returns precisely t. Different t cannot produce
   the same e_t.
6. **Surjectivity.** The proof constructs t from an arbitrary
   f in the fixed-old family and proves literal e_t=f.
   An equal-cardinality assertion without this inverse
   would not be a sufficient substitute.
7. **Certification.** Exact-head Lean compilation, named
   theorem axioms, placeholder scan and independent finite
   regression are required. This is an internal adversarial
   audit, not external peer review.

The Python test exhausts all orientations on up to four vertices,
all legal component rankings and all internal SCC orders.
For each B it compares the *entire set* of fixed-old C_B
enumerations with the image of all B-order updates.
It checks no omissions, no collisions and an explicit
non-fixed-position negative example.

## Next theorem

The canonical complete-code minimum class is a subset of the
fixed-old enumeration family. Under the above bijection, its
preimage is exactly the set of top-SCC choices satisfying the
complete-code test on C_B. Hence that next-choice set has
cardinality g_A(B), independently of the old history.

One auxiliary Lean lemma may be needed to show the canonical
predicate is the same when evaluated at any two generators
of the same actual SCC. The equality of their actual
successor closures and lower parts has already been proved.

The finite history count (#482) and the actual-order data
bijection (#488) are then the appropriate endpoints for
the global finite product. The infinite N₀ big Ramsey
theorem remains separate.
