# Adversarial audit — concrete finite growth class and class closure

15 October 2026. The mathematical definition is

    C_F = { finite graphs G : δ(X) ≥ F(|X|) for every X⊆G },

where δ(X)=2|X|−e(X), and the published growth function F is
continuous, nondecreasing and unbounded with F(0)=0 and the
additional assumptions needed for the C_F free-amalgamation class.

The new Lean predicate GraphOn.IsGrowthSparse F A compares
the real-valued F(s.card) with the integer predimension of
every induced finite s⊆A. It is not replaced by 2-sparsity.

## Four independent adversarial mathematical referees

**1. Definition referee — real values and induced subgraphs.**
The manuscript's F is real-valued, not integer-valued. Lean
therefore uses F : ℕ→ℝ and casts δ(s) : ℤ into ℝ, exactly as
in the mathematical definition at natural arguments. Since
membership tests every finite s⊆A, it is hereditary. If
F(n)≥0 for all natural n, it implies ordinary 2-sparsity.
The converse is false: K4 is 2-sparse (its predimension is
nonnegative on all subsets) but δ(K4)=2<4=F(4) when F(n)=n.

**2. Isomorphism referee — all vertices and all nonedges.**
Class membership must be invariant under induced graph
isomorphism, including reflection of nonedges. For each
finite s, an induced injection preserves both |s| and δ(s).
Every finite intermediate subset of the image is the image
of an intermediate subset of the source. Thus the full
growth inequality transfers in both directions. Ordinary
positive-edge homomorphisms would not suffice.

**3. Free-amalgamation referee — a necessary extra hypothesis.**
Monotonicity and unboundedness of F do NOT force C_F to
be closed under d-closed free amalgamation. Let F(n)=n.
Take two triangles sharing exactly one vertex P and with
no edges between their disjoint tails. Each triangle belongs
to C_F, since every subgraph has at most as many edges
as vertices. P is strictly d-closed in either triangle:
δ(P)=2, while every strict larger subset has δ=3.
Their five-vertex free union has six edges and predimension
4<5=F(5), and is therefore not in C_F.

Hence a free-amalgamation result for the *restricted*
growth class must be a separate standing assumption or
be proved from additional hypotheses on F. This is exactly
how the manuscript formulates its C_F construction.
The Lean predicate GrowthClosedUnderDClosedFreeJoins
records that class-level hypothesis rather than silently
deriving it from the abstract graph-predimension lemmas.

**4. Finite-to-countable referee — the conditional batch step.**
Once the finite tagged batch has been proved strictly
d-closed over its old stage, its class membership can be
established by finite induction *if* the old stage and all
permitted local graph codes belong to C_F and C_F is closed
under the exact d-closed free joins. This uses the old stage's
actual support at every prefix; merely listing finitely many
codes or proving 2-sparsity is insufficient.

Even that finite class-preservation theorem does not supply
the countable level schedule, fair extension property,
graph-reduct identification, block-root functions or monoid
isomorphism.

## Independent executable diagnostic

scripts/check_cf_growth_class.py checks heredity and
induced-image invariance of the real growth inequality
across all labelled graphs with at most four vertices and
several rational-valued growth families. It also verifies
both the K4 strong/strict distinction and the two-triangle
failure of free-amalgamation membership for F(n)=n.

These are bounded falsification checks, not substitutes for
the general Lean proofs. The precise theorem markers may
be promoted only after the final CI build, standard-axiom
audit and proof-placeholder scan pass.
