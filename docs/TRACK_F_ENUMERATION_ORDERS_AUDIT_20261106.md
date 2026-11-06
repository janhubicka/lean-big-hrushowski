# Track F — finite enumerations versus labelled linear orders (6 November 2026)

**Mathematical point.** A finite enumeration (e: \operatorname{Fin}(n)\cong V)
determines a strict linear order on the actual labelled vertex set by
(x <_e y\iff e^{-1}(x)<e^{-1}(y)). Two bijective enumerations of the same
labelled domain produce the same order relation **only when they are
equal**. The proof transports their equality of order relations
to a finite ordinal order automorphism, which Mathlib proves is
the identity.

Consequently the finite code fibre counted by
`N0LocalCodeFibre.localCodeFibre_card` represents exactly that many
*distinct labelled linear order relations*, not merely that many
enumeration objects. This addresses a genuine part of the finite
degree formula's counting correspondence.

**Adversarial referee panel (internal checks):**
1. The order is on the **fixed labelled set**, not on an
   isomorphism-class quotient of unordered copies.
2. Injectivity relies on bijectivity of the enumeration;
   a noninjective listing could repeat labels and invalidate it.
3. Two sinks swapped by an automorphism can have the same directed
   adjacency code but yield distinct labelled orders.
4. The relation satisfies strict irrefl., transitivity and
   totality; empty and one-point domains are included.
5. The count is the **embedding**-oriented count; dividing by
   `|Aut(A)|` for image copies is a later separate convention.
6. This proof still does not assemble entire permitted global
   orders from component prefixes. Require Lean CI, axiom audit
   and the independent finite regression before marking validated.

No manuscript changes. No infinite big Ramsey assertion is proved.
