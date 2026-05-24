import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Thermo.SusceptibilityOnsagerStress
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
import InfoGeometry.Canonical.OnsagerCasimirJ
import InfoGeometry.Canonical.CoadjointCasimirEntropy

/-!
# Erlangen Operator 2.0

This file closes the canonical synthesis theorem:

* Souriau entropy is treated as a generalized Casimir invariant.
* Koszul/Fisher response tensors are the induced invariant geometry.
* Onsager/J reciprocity supplies the operatorial two-form channel.
* The resulting geometry is the symmetry-invariant packet.

This file is a synthesis layer. It does not construct:

* the split Clifford CAR source,
* the split-octonion projective incidence geometry,
* the affine current algebra,
* the Sugawara/Virasoro representation.

Those remain separate owner branches.
-/

namespace InfoGeometry
namespace Canonical

/--
Erlangen Operator 2.0 datum.

This packages the symmetry action, entropy functional, response metric, Onsager
pairing, and Casimir/J-recipient structure without claiming that any lower
layer constructs all the others.
-/
structure ErlangenOperatorDatum
    (𝕜 State Obs : Type*) where
  entropy : State → 𝕜
  responseMetric : State → Obs → Obs → 𝕜
  onsagerPairing : State → Obs → Obs → 𝕜
  symmetryFlow : Obs → State → State
  casimirJ : Obs → Obs

  entropy_invariant :
    ∀ X s, entropy (symmetryFlow X s) = entropy s

  response_invariant :
    ∀ X A B s,
      responseMetric (symmetryFlow X s) A B =
        responseMetric s A B

  onsager_reciprocity :
    ∀ A B s,
      onsagerPairing s A B =
        onsagerPairing s (casimirJ B) (casimirJ A)

theorem erlangen_entropy_is_generalized_casimir
    {𝕜 State Obs : Type*}
    (E : ErlangenOperatorDatum 𝕜 State Obs) :
    IsGeneralizedCasimir E.entropy E.symmetryFlow := by
  intro X s
  exact E.entropy_invariant X s

theorem erlangen_responseMetric_is_geometry_invariant
    {𝕜 State Obs : Type*}
    (E : ErlangenOperatorDatum 𝕜 State Obs) :
    IsGeometryInvariant E.responseMetric E.symmetryFlow := by
  intro X A B s
  exact E.response_invariant X A B s

/--
Bundled Erlangen 2.0 geometry closure data.
-/
structure ErlangenOperatorGeometry
    {𝕜 State Obs : Type*}
    (E : ErlangenOperatorDatum 𝕜 State Obs) where
  entropy_is_casimir :
    IsGeneralizedCasimir E.entropy E.symmetryFlow
  response_is_geometry :
    IsGeometryInvariant E.responseMetric E.symmetryFlow
  onsager_has_J_reciprocity :
    ∀ A B s,
      E.onsagerPairing s A B =
        E.onsagerPairing s (E.casimirJ B) (E.casimirJ A)

/--
Erlangen Operator 2.0 closure theorem.

Entropy is a generalized Casimir invariant, and the induced response geometry
is invariant under the same operator symmetry, with Onsager/J reciprocity.
-/
theorem geometry_as_symmetry_invariants
    {𝕜 State Obs : Type*}
    (E : ErlangenOperatorDatum 𝕜 State Obs) :
    ErlangenOperatorGeometry E :=
{
  entropy_is_casimir := erlangen_entropy_is_generalized_casimir E
  response_is_geometry := erlangen_responseMetric_is_geometry_invariant E
  onsager_has_J_reciprocity := by
    intro A B s
    exact E.onsager_reciprocity A B s
}

theorem erlangen_operator_geometry_closure
    {𝕜 State Obs : Type*}
    (E : ErlangenOperatorDatum 𝕜 State Obs) :
    ErlangenOperatorGeometry E :=
  geometry_as_symmetry_invariants E

end Canonical
end InfoGeometry
