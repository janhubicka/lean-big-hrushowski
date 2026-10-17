# Adversarial audit: root forcing for minimal closure blocks
17 October 2026

## Exact mathematical claim

For a finite predimension on an arbitrary vertex type, let (A\subseteq B\subseteq C) be finite sets and let (X\subseteq C) be **strong in C**, or respectively **strictly d-closed in C**. If (A\subseteq X), the extension (A\preccurlyeq B) is minimal for the same relation, and some (r\in (B\setminus A)\cap X), then (B\subseteq X).

The key strengthening beyond the first proposed proof is that **B need not be closed in C**. By submodularity, for every (Ysubseteq B) containing (X\cap B):
[
\delta(X\cup Y)+\delta(X\cap Y)\le\delta(X)+\delta(Y).
]
Here (X\cap Y=X\cap B). If (Y\ne X\cap B), then (X\cup Y\ne X), and strict d-closedness of (X) makes the inequality strict in the desired direction. The same calculation with a weak inequality works for strongness. Thus (X\cap B\preccurlyeq B), and minimality forces (X\cap B=B).

A finite **rooted minimal d-closed chain** carries a root in the designated finite root set from each minimal increment. Its last vertex set is the d-closed hull, inside that final set, of the initial base and the selected roots. This is an abstract finite theorem, not yet the full infinite (C_F) functional equation.

## Eight hostile checks

1. **Assumption minimization:** The original version needlessly required B to be closed in C. This assumption has been removed; finite intersection-restriction is proved directly from the predimension submodularity axioms. No hidden global B-closedness survives.
2. **Strictness:** In the strict case (Y\supsetneq X\cap B) means (X\cup Y\supsetneq X); hence strictness of X in C is applicable. Weak self-sufficiency would prove only the weak version and is not silently substituted.
3. **Minimality:** The notion is *minimal closed intermediate*, not inclusion-minimal as a vertex set alone. If the root is in X but outside A, the intersection cannot equal A; the only remaining possibility is B.
4. **Ambient:** X is explicitly closed **in C** and B is merely a subset of C. If X is not closed in C, the conclusion need not hold (take the six-vertex triangle-component example from the manuscript, let X consist of the old base plus only one fresh vertex).
5. **Roots:** Each increment is required to meet the designated root set outside its old base. Missing a root invalidates the generation theorem (the one-vertex strict extension over empty base is a negative control).
6. **Termination:** The generation chain is finite and structurally inductive. No `omega`-length enumeration, finite support scheduling, birth labels or Ramsey theorem is smuggled into the statement.
7. **Closure computation:** The theorem computes `dClosedHull (a ∪ roots) b` in the **finite** final ambient b. To deduce (H(R(v))=C(v)) in the countable limit, one still needs the actual selected-block rooted-chain certificate and finite-to-global hull comparison.
8. **Implementation:** The C0 and CF corollaries invoke **one** relation-parametric intersection argument; the weak/strict intersection-restriction lemmas remain separately proved because their inequalities differ. A green marker requires the exact Lean build, `#print axioms` report, and no-placeholder scan for all new declarations.

These are independent *roles* of internal adversarial review, not independent human referees or separately spawned agents. Do not promote the manuscript's full block-root recovery proposition on the strength of this finite lemma alone.
