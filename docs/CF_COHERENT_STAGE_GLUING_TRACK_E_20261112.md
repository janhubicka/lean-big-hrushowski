# Track E: gluing coherent finite birth-stage embeddings

12 November 2026. This lemma separates the **countable passage**
from the still-open compatibility/uniqueness step in the actual
\(\mathcal C_F\) lifting construction.

## The exact conclusion

Write \(U_n\) for the literal finite stage of the birth-labelled
\(\mathcal C_F\) construction. Every vertex belongs to \(U_{n+1}\)
when its birth level is \(n\), and each \(U_n\) is closed
under the entire auxiliary b-function.

Suppose, for each \(n\), we are given an induced ordered b-embedding

\[
 e_n:U_n\longrightarrow M_F^\dagger
\]

preserving **the complete auxiliary b-values**, the birth-level
preorder, and the canonical birth order. Assume that all \(e_n\)
act on birth levels by the *same* map \(h\), and agree literally
on the nested old stages:

\[
e_m|_{U_n}=e_n \qquad (n\le m).
\]

Then the union \(e=\bigcup_n e_n\) is a genuine countable
ordered b-embedding. For every vertex \(v\), its value is simply

\[
e(v)=e_{b(v)+1}(v),
\]

where \(b(v)\) denotes its literal birth level.

The complete b-value equation follows by working inside
\(U_{b(v)+1}\), which contains the entire value \(b(v)\).
Similarly, two vertices lie together in
\(U_{\max(b(u),b(v))+1}\); injectivity, inducedness,
and the two order clauses follow from that stage.

This is an **unconditional gluing lemma once the coherent family
is supplied**, not a proof that the constructed prescribed finite
lifts are coherent.

## Internal adversarial referee panel

1. **Well-definedness.** Every vertex appears at a literal birth
   stage. No arbitrary isomorphic representative or global
   enumeration is chosen. The comparison lemma proves equality
   with every later stage.
2. **Injectivity.** If two vertices have equal union images,
   choose one actual stage containing both and use injectivity
   of that finite map. Injectivity of each finite map *alone*
   would not suffice without compatibility.
3. **Induced graph.** An edge and a nonedge are both witnessed
   inside one finite stage. The source graph is the induced
   subgraph of the countable graph there.
4. **Complete functional values.** The entire b-value of a
   vertex lies in its finite birth stage. The formal proof uses
   the certified equality between the finite restricted b-value
   and the full ambient value. Checking only immediate old
   adjacency is insufficient.
5. **Orders and levels.** The canonical birth order and the
   birth-level preorder are preserved and reflected on the
   common stage of any pair. The level action is read from
   the first stage containing the vertex; no order-type
   assumption on the image is added.
6. **Empty stage and cutoffs.** \(U_0\) may be empty. The proof
   uses \(b(v)+1\), so no vertex is prematurely assigned an
   image at a stage where it has not appeared.
7. **Uniqueness and coherence.** The theorem's input includes
   exact compatibility of all finite maps. The finite
   prescribed lifting theorem currently provides existence,
   but not this compatibility. A future finite uniqueness
   theorem can supply it after proving that restricting a
   larger finite embedding to a closed smaller stage is still
   an embedding with the *full* b-values.
8. **Ramsey-space boundary.** A global b-embedding is not by
   itself an identification of the functional copy space or
   its finite approximation system. The actual R/H language,
   the range formula, composition of lifted maps, and the
   Ellentuck axioms remain downstream.
9. **Verification trust.** These are separate mathematical
   challenge roles conducted internally, not external human
   referees. Exact Lean compilation, the standard-axiom
   audit, and the repository placeholder scan must pass
   before promotion.

## Next steps

The most economical path appears to be:

- Prove hereditary restriction of a genuine finite ordered
  b-embedding to a **b-closed** subset of its source.
- Show that canonical finite prescribed lifts at nested
  birth stages agree, either directly from the recursion
  or by invoking the finite uniqueness theorem now under
  development in Track B.
- Apply this gluing result to obtain the countable lift
  with its exact level action.
- Combine it with the conditional complete-support
  range equation and the already-certified synthetic
  omega-level Ellentuck transport.

No manuscript statement or validation marker has been
promoted by this branch.
