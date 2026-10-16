# Adversarial audit: canonical old support as an actual finite subtype

16 October 2026

The established canonical_dClosed_local_support lemma returns the
least strict d-closed hull T of the old neighbours of B inside the
actual old vertices A of a minimal finite extension. The new module
identifies T with a *literal finite subset P of the old vertex type S*
rather than silently treating a Finset of Sum S B as a Finset S.

In a complete old/fresh presentation S⊕B, define P to contain
exactly those s∈S whose old-tagged vertex Sum.inl s lies in T.
The proof uses T⊆A to show P.image Sum.inl=T exactly. This
provides the bridge needed by the newer named-support and complete
one-block response theorems.

Under the minimal strict extension A<_d S⊕B, the existing
canonical support theorem gives:

  P≤d S;
  every old neighbour of a fresh vertex lies in P;
  P<_d P⊕B is minimal (as the induced interval in S⊕B);
  P is exactly the strict d-closed hull of the old-neighbour set
  computed within its own local old carrier.

## Five deliberately hostile mathematical tests

1. **Sort distinction.** The canonical closure T is a
subset of Sum S B, whereas the required support P is a
subset of S. One must prove exact image equality,
including ruling out every fresh Sum.inr vertex of T.
They cannot be interchanged definitionally.

2. **Strictness.** The local interval is minimal strictly
d-closed, not merely a weakly strong inclusion.
The proof reuses canonical_dClosed_local_support with
exact induced old and fresh finite sets.

3. **Back neighbours.** It is not enough to know P is
closed. We must prove every old neighbour of a fresh
vertex lies in P, so the new block can be freely
amalgamated with a larger prescribed old source over P.

4. **Hull equality.** The old-neighbour set over T equals
the original old-neighbour set over A only because
the entire latter set is already contained in T.
Without checking this equality, exact support in the
local graph would not follow.

5. **Remaining local split transport.** This module
proves minimality and exact old support in the original
graph with induced subset P.image Sum.inl. The complete
local graph on the split subtype carrier P⊕B must still
transport these interval properties, growth membership
and fresh cardinality. That is a separate reusable
and deliberately visible proof obligation.

No countable genericity is claimed. Mark any statement
green only after final integrated Lean compilation,
standard-axiom and placeholder checks. The referee
passes are separated internal adversarial mathematical
checks, not independent external human certification.
