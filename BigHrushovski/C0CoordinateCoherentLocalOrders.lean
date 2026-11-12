import BigHrushovski.C0CoordinateCanonicalLocalRepresentative

/-!
# Hereditary compatibility of the chosen local ordered representatives

Choosing one ordered representative separately for every local type
is NOT enough to construct the coordinate host. The choice must be
coherent when restricting a chosen type to the complete one-generated
closure of any vertex. In particular the induced order on that closure
must be a selected ordered type, and the lower part must agree with
the intrinsic decomposition by complete unary C-values.

We give this condition as an explicit predicate on a catalogue of
selected representatives. We do NOT assume it follows from an
arbitrary catalogue, require all automorphisms to preserve an order,
or claim to have constructed a catalogue covering the C₀ finite age.

The missing existence theorem must select these types recursively,
using the already ordered lower part of each local closure.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {I : Type*}

/-- The local choices agree on all one-generated restrictions. For a
chosen representative of type i and any point a, its complete unary
closure must have *some* selected type j, with an increasing
isomorphism preserving the entire induced graph, complete unary
values, and intrinsic lower part.

The comparison is existential in the isomorphism, NOT universal over
all unordered automorphisms. -/
def ChosenLocalOrders.IsHereditary (c : ChosenLocalOrders I) : Prop :=
  ∀ (i : I) (a : Fin (c.size i)),
    ∃ j : I,
      ∃ f : Fin (c.size j) ≃ (c.representative i).value a,
        (∀ u v : Fin (c.size j),
          (c.representative j).graph.adj u v ↔
            (c.representative i).graph.adj
              (f u).val (f v).val) ∧
        (∀ u v : Fin (c.size j),
          v ∈ (c.representative j).value u ↔
            (f v).val ∈ (c.representative i).value (f u).val) ∧
        (∀ u v : Fin (c.size j),
          u < v ↔ (f u).val < (f v).val) ∧
        (∀ u : Fin (c.size j),
          u ∈ (c.representative j).lower ↔
            (c.representative i).value (f u).val ≠
              (c.representative i).value a)

/-- A local-order catalogue with an EXPLICIT hereditary certificate.
The existence of such a complete catalogue for all permitted finite
C₀ types is a separate mathematical obligation, not an axiom hidden
in a theorem about the host. -/
structure HereditaryLocalOrders (I : Type*) where
  choices : ChosenLocalOrders I
  restriction_compatible : choices.IsHereditary

end FiniteUnaryCoordinates
end BigHrushovski
