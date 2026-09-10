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

def carrierSolderAlg :
    InfoGeometry.Physics.ChiralCausalCone.M2C ≃ₐ[ℂ]
      ChiralCausalCone.M2C := (AlgEquiv.refl : Carrier ≃ₐ[ℂ] Carrier)

theorem carrierSolder_apply (A : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolder A = A := rfl

theorem carrierSolder_mul (A B : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolder (A * B) = carrierSolder A * carrierSolder B := rfl

theorem carrierSolderAlg_apply (A : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolderAlg A = A := by
  change A = A
  rfl

theorem carrierSolderAlg_symm_apply (A : ChiralCausalCone.M2C) :
    carrierSolderAlg.symm A = A := by
  change A = A
  rfl

theorem carrierSolderAlg_left_inverse (A : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolderAlg.symm (carrierSolderAlg A) = A := by
  exact carrierSolderAlg.symm_apply_apply A

theorem carrierSolderAlg_right_inverse (A : ChiralCausalCone.M2C) :
    carrierSolderAlg (carrierSolderAlg.symm A) = A := by
  exact carrierSolderAlg.apply_symm_apply A

theorem carrierSolderAlg_commutator
    (A B : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolderAlg (A * B - B * A) =
      carrierSolderAlg A * carrierSolderAlg B -
        carrierSolderAlg B * carrierSolderAlg A := by
  simp only [map_sub, map_mul]

theorem carrierSolder_commutator (A B : InfoGeometry.Physics.ChiralCausalCone.M2C) :
    carrierSolder (A * B - B * A) =
      carrierSolder A * carrierSolder B - carrierSolder B * carrierSolder A := rfl

theorem sigmaPlus_solder :
    carrierSolder InfoGeometry.Physics.ChiralCausalCone.σPlus =
      ChiralCausalCone.σPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rfl

theorem sigmaPlus_alg_solder :
    carrierSolderAlg InfoGeometry.Physics.ChiralCausalCone.σPlus =
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

theorem sigmaMinus_alg_solder :
    carrierSolderAlg InfoGeometry.Physics.ChiralCausalCone.σMinus =
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

theorem sigmaThree_alg_solder :
    carrierSolderAlg InfoGeometry.Physics.ChiralCausalCone.σ3c =
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
