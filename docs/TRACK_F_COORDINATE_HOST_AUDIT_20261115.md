# Track F: adversarial audit of the coordinate host and return map

15 November 2026. Based on *The big Hrushovski*, manuscript v52,
§7.4.4, especially Lemmas 7.18–7.19 (printed pp. 52–53).
The TeX manuscript and its validation markers are unchanged.

## Precise issue: the coordinate relation is not a linear order on W

The proof forms a coordinate host W of equivalence classes of triples
\([D,x,e]\), where D is a finite *permitted* one-generated successor
closure, x generates it, and e:D→ω is increasing. It defines
\(\pi([D,x,e])=e(x)\), and \(u\triangleleft v\) iff \(\pi(u)<\pi(v)\).

This relation is **not a global linear order on W**. Injectivity of
\(\pi\) fails even when all coordinate maps e are individually
injective. Here is a witness within the stated finite orientation
class, taking distinct points a,b:

- \(D_1=\{a\}\), with e₁(a)=1, x₁=a;
- \(D_2=\{a,b\}\) with the single arrow a→b, with e₂(b)=0,
  e₂(a)=1, x₂=a. This is a permitted one-generated closure
  with P={b} ordered before its top singleton {a}.

The two triples are distinct in W (their generated closures have
different cardinalities), but \(\pi(u)=\pi(v)=1\). Thus neither
u◁v nor v◁u. This is an obstruction to *global totality*, not to
using the relation on finite ordered images.

**Repair/clarification for the English proof.** State explicitly:
\(\triangleleft\) is a binary relation on the coordinate host,
not asserted to be a linear order on all of W. Its restriction to the
image of every *increasing coordinate assignment* from a permitted
finite ordered closed structure is a linear order isomorphic to the
original order. The target W need not belong to the class of
linearly ordered finite structures: \(\operatorname{Emb}(A^*,W)\)
means embeddings preserving/reflection the \((\Sigma,C)\)-structure
and preserving the required \(\triangleleft\)-comparisons on
the image. The statement \(\operatorname{Emb}(A^*,W)\leftrightarrow
[\omega]^{|A|}\) requires this interpretation.

The return map ψ:W→N₀ from the manuscript is not globally
order-preserving for \(\triangleleft\), and should **not** be claimed
to be such. The needed statement is weaker and more precise:
for every permitted finite closed D* and every increasing-coordinate
embedding f:D*→W, the composite ψf is ordered, successor-closed
and respects the full \((\Sigma,C)\)-data. This is what makes
ψT_hφ an ordered self-embedding and permits Ramsey colouring on
\([\omega]^{|A|}\).

## Other proof obligations to verify independently

**1. Well-defined closure representatives.** For a triple
[D,x,e], each y∈D is represented by
\([C_D(y),y,e|_{C_D(y)}]\). Prove that this is independent of
the chosen presentation of the equivalence class, and that
taking closure values commutes with restriction. The complete
Σ- and C-values at the pointed vertex must be recovered
literally, not just up to an unordered isomorphism.

**2. Finite overlap compatibility.** Arbitrary unions of
coordinate triples need not be globally ordered. Verify that
every *finite successor-closed union in the functional
reduct* is an allowed finite orientation with all complete
outgoing sets and closure values unchanged. The finite
2-orientation bound is local to each pointed closure, but
compatibility on overlapping closure representatives is
required to prevent contradictory outgoing sets.

**3. Finite-to-one component maxima.** The enumeration of
W-components by maximum coordinate requires that only
finitely many components have maximum coordinate ≤n.
This must count full labelled pointed closure types and
coordinate assignments and justify that every closure
vertex has coordinate ≤ that maximum. The manuscript's
argument is plausible, but requires an explicit bound
or a finite-type lemma for a formal proof.

**4. Lower components precede their upper components.**
Every arrow successor lies in the pointed closure and occurs
earlier in its permitted ordering. Verify that the induced
component preorder on W has no dependency cycle across
distinct components and that the maximum coordinate is
strictly smaller on every strict successor component.
This ensures the recursive return-map construction can
embed all of P_B before B.

**5. Nonedges in the return embedding.** At each recursive
step, a permitted one-component extension over its true
lower part is freely amalgamated with the already embedded
finite closed portion. Verify *absence* of accidental arrows
into previously embedded components outside P_B, not only
preservation of outgoing arrows.

**6. Comparisons between components.** For an image of a
permitted finite ordered closed D*, the coordinate assignment
is increasing on the full domain and SCCs are intervals.
Hence the order of different SCCs agrees with the order
of their maximum coordinates. This conclusion is for those
images, **not for arbitrary finite subsets of W**.

**7. Finite versus infinite conclusions.** A successful
finite canonical-order count only supplies the number of
colours. Lemma 7.18 (recurrence/finite realization) and
Lemma 7.19 (degree-one ordered Ramsey property) remain
logically separate and require their own formal audits
before Theorem 7.17 is validated. In particular the fact
that the cardinality formula is correct does not establish
the infinite big Ramsey degree by itself.

## Adversarial referee panel

Seven internal challenge roles were applied: coordinate-order
totality, presentation independence, overlap of closure values,
component-maxima finiteness, successor precedence, free-amalgam
reflection of nonedges, and exact infinite counting scope.

The coordinate-tie counterexample above is constructive.
The remaining six items are *proof obligations*, not
assertions that the manuscript is incorrect. They should
be checked in English before beginning or promoting a
Lean validation marker for the infinite result. These
role-separated checks are not independent external human
referee reports.

## Suggested concise manuscript edit, when the proof section is unfrozen

After the definition of ◁, insert:

> This relation need not be a linear order on W, since different
> pointed closure codes may have the same coordinate. We use it
> only on images of permitted finite ordered closed structures
> arising from increasing coordinate assignments, where it is
> precisely the prescribed linear order. Similarly, the return
> map below is order-preserving on these images, not globally
> on W.

Do not add this text to the manuscript yet without checking
whether the latest TeX version already contains an equivalent
qualification. No change to mathematical statements of
Lemmas 7.18–7.19 is proposed in this audit.
