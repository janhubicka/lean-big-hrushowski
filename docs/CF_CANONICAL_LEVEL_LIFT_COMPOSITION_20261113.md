# Track E — composition of canonical countable level lifts

13 November 2026. This extension is stacked on PR #494, the
actual countable ordered b-lift theorem.

## Statement

For every strictly increasing map \(h:\mathbb N\to\mathbb N\),
the verified finite rigidity theorem, combined with coherent
finite-stage gluing, provides a unique **ordered b-embedding**
\(f_h\) of the actual countable \(\mathcal C_F\) birth structure
whose birth-level action is \(h\). The image is the exact
full-support domain \(U[\operatorname{range}(h)]\).

This note adds the compatibility laws:

\[
f_{\mathrm{id}}=\mathrm{id},
\qquad
f_{k\circ h}=f_k\circ f_h.
\]

The proof is short once the correct theorem is available:
both sides preserve the induced graph, complete b-values,
the actual canonical order and birth-level preorder. Both
have the same strictly increasing birth-level action.
Finite uniqueness, applied through the countable limit,
forces the two maps to agree.

The composition statement is **not** a claim that every
embedding of the paper's partial (R,H) language is already
one of these maps. Recognizing the birth-level action of all
such embeddings remains a separate theorem.

## Adversarial referee panel — internal mathematical checks

**1. Exact unary values.** Composition must carry every
complete finite b-value onto the full target b-value.
The proof explicitly uses finite-set image composition and
both exact b-value equalities; mere inclusions would not
suffice.

**2. Induced graph.** The adjacency relation is preserved
and reflected. Composition of two iff statements yields
the required iff, including all nonedges.

**3. Order.** The actual canonical birth order and the
birth-level preorder are both preserved and reflected.
No substitute order on selected representative roots is used.

**4. Level action.** The composition \(f_k\circ f_h\)
sends birth level \(n\) to \(k(h(n))\), not to
\(h(k(n))\). The order of composition is checked
against the exact formula for the images.

**5. Strict increase.** If \(h,k\) are strictly
increasing, then \(k\circ h\) is strictly increasing.
No surjectivity or global inverse is required.

**6. Empty or skipped stages.** Both global maps are
constructed from the exact birth carrier, including
arbitrarily large gaps in their image-level sets.
The composition proof makes no assumption that a
fixed birth stage is mapped to a consecutive stage.

**7. Proof of identity.** The identity function is
verified directly to satisfy the complete ordered
b-embedding predicate, and then identified with the
canonical lift by uniqueness, rather than by assuming
a particular implementation of the chosen lift.

**8. Monoid scope.** The laws provide a canonical
composition-preserving assignment from strictly
increasing level maps to ordered b-self-embeddings.
The assertion that this is an isomorphism onto
*all* embeddings needs recognition of their level
action and proof that no birth levels are omitted.

**9. Functional language.** The paper uses R and
a **partial** operation H. The present results are
in the auxiliary b-language; its equivalence to
the full countable (R,H) embedding notion must be
checked separately, including reflection of the
domain of H.

**10. Trust.** These reviews are independent
mathematical challenges run internally, not
externally recruited referees. The theorem remains
a candidate until an exact-head Lean build, six
standard-axiom inspections and a placeholder scan
have succeeded.

## Integration

The module imports only the actual countable
b-lifting endpoint on the parent branch. No
manuscript statement or validation marker is
changed by this PR.
