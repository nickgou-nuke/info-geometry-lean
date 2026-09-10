import InfoGeometry.Canonical.ChiralCausalCone
import InfoGeometry.Physics.ChiralCausalCone

/-!
The canonical chiral cone and the namespaced physics chiral cone use the same
`2 × 2` matrix carrier.  This file records the soldering explicitly, so users
can move between the two APIs without duplicating matrix constructions.
-/

namespace InfoGeometry.Canonical.ChiralCausalConeSoldering

abbrev Carrier := Matrix (Fin 2) (Fin 2) ℂ

def carrierSolder :
    InfoGeometry.Physics.ChiralCausalCone.M2C ≃ₗ[ℂ]
      ChiralCausalCone.M2C := LinearEquiv.refl ℂ Carrier

theorem carrierSolder_apply (A : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolder A = A := rfl

theorem sigmaPlus_solder :
    carrierSolder InfoGeometry.Physics.ChiralCausalCone.σPlus =
      ChiralCausalCone.σPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

theorem sigmaMinus_solder :
    carrierSolder InfoGeometry.Physics.ChiralCausalCone.σMinus =
      ChiralCausalCone.σMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

theorem sigmaThree_solder :
    carrierSolder InfoGeometry.Physics.ChiralCausalCone.σ3c =
      ChiralCausalCone.σ3c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

theorem solder_preserves_causal_determinant (t x y z : ℂ) :
    Matrix.det (carrierSolder
      (InfoGeometry.Physics.SolderingSpinConnectionBogoliubov.solder t x y z)) =
      t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
  exact InfoGeometry.Physics.SolderingSpinConnectionBogoliubov.solder_det t x y z

end InfoGeometry.Canonical.ChiralCausalConeSoldering
