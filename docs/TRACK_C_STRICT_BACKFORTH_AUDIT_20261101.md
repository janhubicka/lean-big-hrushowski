# Track C — strictly d-closed back-and-forth core (1 November 2026)

This branch is **independent** of PR #269: it uses only existing main imports.
The purpose is to re-use the verified C_0 coherent-union API *without*
silently weakening C_F's strict d-closed embeddings.

## Exact endpoints

`CFDClosedBackAndForth.PartialIso` stores two finite globally strictly
d-closed domains, a finite equivalence, and inducedness (both edges and
nonedges). `toStrong` forgets strictness only for the union theorem.

`exists_induced_equiv_of_joint_steps` is conditional on:
- globally strict d-closedness of the empty set in both countable graphs;
- `HasJointSteps` **for every** strictly d-closed finite partial
  isomorphism and **every** next source/target vertex.

Under these exact hypotheses it yields an induced bijection of ℕ.
`equivOfJointSteps_initial` shows prescribed initial values survive.

The omitted argument, **not** claimed here, is deriving
`HasJointSteps` from finite C_F extension responses and finite
globally strict d-closed covers. That will require the finite-source
growth-membership restriction and actual global strict d-closed
transport. It must not use the strong C_0 extension property.

## Adversarial role checks

1. *Closure referee:* a globally strong but not strictly d-closed
   finite domain is not admitted to `PartialIso`. Conversion to
   `FiniteStrongPartialIso` is one-way, only at the union interface.
2. *Empty-base referee:* finite strict closed cover alone does not
   imply that ∅ itself is globally strictly closed, so it is an
   explicit hypothesis of the uniqueness criterion.
3. *Inducedness referee:* source/target inducedness is an ↔
   relation and is preserved by the imported coherent-union theorem.
4. *Map referee:* partial maps retain exact old values and both
   source and target inclusions. No arbitrary strong map can enter
   the strict recursion.
5. *Certification referee:* CI must compile the new module and
   `#print axioms` endpoints. No paper marker may be promoted for
   a conditional strict joint-step criterion alone.

## Non-claims

This PR does **not** prove the concrete `C_F` generic, construct
a joint step, prove the singleton request, adapt F's published
nonnegative domain, or identify the finite level embedding monoid.
The theorem only removes the need to reprove the infinite coherent
union / exact initial value preservation separately for C_F.

Status at creation: **Lean implementation awaiting exact CI**;
internal, role-separated audit only (not external referees).
