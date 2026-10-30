# Adversarial audit: complete old-fresh boundary with partial C_F maps

30 October 2026

## Exact statement

For a finite selected old source S and P⊆S, an injective map
e:S→V transports a local graph over P to the named-base graph
over its literal image Q=e[P]. The old-fresh boundary is
preserved and reflected on every old u∈S and each fresh
ordinal, including the absence of edges outside P.

The theorem does not assume a total function U→V, and remains
meaningful when U is nonempty while S=V=∅.

## Hostile checks

1. **Reverse boundary:** A target old-fresh edge gives a
   support vertex q∈Q. Its unique preimage p∈P under the
   support equivalence satisfies e(p)=e(u). Injectivity
   of e on the selected subtype implies p=u; this is
   what reflects nonedges outside the named support.
   Omitting injectivity would make this argument false.

2. **Complete graph:** The local graph is transported by
   namedBaseGraph, an induced pullback, not merely by a
   positive-edge homomorphism. The biconditional covers
   every boundary edge and nonedge. Fresh-fresh bits are
   handled by the existing namedBaseGraph_fresh_iff theorem.

3. **Partial source:** No code path constructs or invokes a
   total U→V map or an arbitrary target vertex. The
   empty-target case therefore requires no exception
   or distinguished dummy point.

4. **Formalization boundary:** This is a local graph theorem.
   It does not construct the target request, prove its
   d-closed support, establish tag injectivity or
   inducedness of the full selected batch. Those are
   separate interfaces; the current next step is to
   instantiate this lemma at the actual partial target
   request and invoke selectedTargetMapSubtype_induced.

5. **Lean check:** One exact axiom endpoint is recorded.
   A full Lean build, standard axiom audit, placeholder
   scan and finite regressions must pass on the same
   revision before certification.

These are role-separated adversarial mathematical checks
within the project, not external independent referee reports.
