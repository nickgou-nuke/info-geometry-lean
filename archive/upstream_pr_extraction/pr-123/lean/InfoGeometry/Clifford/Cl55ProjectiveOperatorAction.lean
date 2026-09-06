import InfoGeometry.Clifford.Cl55CAROperatorTransport
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone

/-!
# Projective readout of the noncommutative doubled carrier

The projective statement is formulated on real rays of the doubled module.
No division by an operator-valued component is used.  Matrix transport and
Spin transport both descend to representative-level projective rays.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.OperatorAlgebra.KreinIsotropicCone

theorem matrixAction_preserves_cl55_projective_ray
    (A : Cl55OperatorMatrix)
    {v w : Fin 2 → Cl55}
    (hvw : SameProjectiveRay v w) :
    SameProjectiveRay (matrixAction A v) (matrixAction A w) := by
  rcases hvw with ⟨lam, hlam, rfl⟩
  refine ⟨lam, hlam, ?_⟩
  exact (matrixAction A).map_smul lam v

theorem spinTransportCarrier55_preserves_projective_ray
    (g : Spin55)
    {v w : Fin 2 → Cl55}
    (hvw : SameProjectiveRay v w) :
    SameProjectiveRay (spinTransportCarrier55 g v)
      (spinTransportCarrier55 g w) := by
  rcases hvw with ⟨lam, hlam, rfl⟩
  refine ⟨lam, hlam, ?_⟩
  funext i
  change spinCARAutomorphism g (lam • v i) =
    lam • spinCARAutomorphism g (v i)
  change InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
      (spinGroup.toUnits g) (lam • v i) =
    lam • InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation
      (spinGroup.toUnits g) (v i)
  exact InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul
    (spinGroup.toUnits g) lam (v i)

theorem spinTransportMatrix55_preserves_projective_action
    (g : Spin55) (M : Cl55ElementMatrix)
    {v w : Fin 2 → Cl55}
    (hvw : SameProjectiveRay v w) :
    SameProjectiveRay
      (matrixAction (spinTransportMatrix55 g M)
        (spinTransportCarrier55 g v))
      (matrixAction (spinTransportMatrix55 g M)
        (spinTransportCarrier55 g w)) := by
  exact matrixAction_preserves_cl55_projective_ray _
    (spinTransportCarrier55_preserves_projective_ray g hvw)

end InfoGeometry.Clifford.Clifford55
