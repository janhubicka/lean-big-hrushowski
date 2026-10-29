# Adversarial audit: actual simultaneous C_F tagged-batch transport

29 October 2026

## New finite statements

For a selected family D of source requests supported in a finite old
substructure S, the target request tag is not an arbitrary function:
it is the actual transportGrowthStageRequest. The complete source
support is mapped to its literal image, and all fresh ordinals are
identified by the canonical Fin.castOrderIso arising from equality
of the source and target request sizes.

The request-tag map is injective by exact named-code noncollision.
The within-block ordinal map is an order isomorphism, so it is
injective and surjective and preserves every ordinal value.
Consequently the entire selected old+fresh map is injective and its
image is strictly d-closed in the whole target tagged next level,
provided the old image is d-closed there.

## Four hostile checks

1. **Tag integrity.** Two source requests with equal abstract
   graph types but different literal named supports must remain
   distinct. The proof invokes the actual complete-code
   injectivity theorem, not just equality of block sizes or
   graph isomorphism types.

2. **Ordinal integrity.** A fresh block of size n is mapped
   onto a fresh block of exactly size n. The natural ordinal
   map is an increasing *bijection*; injectivity alone is
   insufficient to identify the complete target image.
   The identity of Fin values follows from Fin.castOrderIso.

3. **Predimension.** The required support image Q=f[P] is
   strictly d-closed in the target old stage by an explicit
   hypothesis. Strict d-closedness of the old image f[S]
   is a *separate* hypothesis in the global-in-level closure
   conclusion. A mere order map of S does not imply it.
   The selected-subbatch theorem establishes closure after
   all target blocks have been attached simultaneously.

4. **Graph/order boundary.** This module does not assert
   inducedness or preservation of the exact finite stage
   order. The existing generic batch theorem gives the
   inducedness criterion; the remaining old-fresh and
   fresh-fresh equivalences must be derived from the
   constructed local request graphs and their exact supports.
   The request lex theorem gives the block comparison but
   still needs to be combined with old/new and ordinal
   cases for the actual total order.

## Lean verification and remaining steps

Four exact axiom endpoints are registered. A full successful
Lean build, standard-axiom audit, placeholder scan and all
finite regressions are necessary before green markers are
attached to the manuscript.

After this lemma, complete same-level finite lifting requires
local old-fresh and fresh-fresh induced graph comparisons,
the resulting global inducedness and stage-order equivalence,
and preservation of the complete b-values. Finite unique
level lifting and the countable embedding monoid remain
unverified.

These checks use separate adversarial mathematical roles,
not independent human referees.
