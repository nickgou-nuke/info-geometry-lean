import InfoGeometry.HodgeCohomology.KreinGreenEnergy
import InfoGeometry.Canonical.HodgeGreenProjectorConstructionTests

namespace InfoGeometry.HodgeCohomology.KreinGreenEnergy.Tests

open InfoGeometry.Canonical.HodgeGreenProjectorConstruction.Tests

noncomputable section

def signedPairing : LinearMap.BilinForm ℝ Triple :=
  let first := LinearMap.fst ℝ ℝ (ℝ × ℝ)
  let second := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let third := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  first.smulRight first + second.smulRight second - third.smulRight third

theorem signedPairing_apply (left right : Triple) :
    signedPairing left right = left.1 * right.1 + left.2.1 * right.2.1 - left.2.2 * right.2.2 :=
  rfl

theorem signedPairing_symmetric : signedPairing.IsSymm := by
  constructor
  intro left right
  simp only [signedPairing_apply]
  ring

theorem signedPairing_nondegenerate : signedPairing.Nondegenerate := by
  constructor
  · intro state orthogonal
    have first : state.1 = 0 := by simpa [signedPairing_apply] using orthogonal (1, 0, 0)
    have second : state.2.1 = 0 := by simpa [signedPairing_apply] using orthogonal (0, 1, 0)
    have third : state.2.2 = 0 := by simpa [signedPairing_apply] using orthogonal (0, 0, 1)
    exact Prod.ext first (Prod.ext second third)
  · intro state orthogonal
    have first : state.1 = 0 := by simpa [signedPairing_apply] using orthogonal (1, 0, 0)
    have second : state.2.1 = 0 := by simpa [signedPairing_apply] using orthogonal (0, 1, 0)
    have third : state.2.2 = 0 := by simpa [signedPairing_apply] using orthogonal (0, 0, 1)
    exact Prod.ext first (Prod.ext second third)

theorem differential_adjoint :
    LinearMap.IsAdjointPair signedPairing signedPairing tripleSystem.d tripleSystem.δ := by
  intro left right
  simp [signedPairing_apply, tripleSystem, differential, codifferential]

theorem green_adjoint :
    LinearMap.IsAdjointPair signedPairing signedPairing tripleSystem.Δ tripleSystem.Δ := by
  intro left right
  simp [signedPairing_apply, tripleSystem, differential, codifferential, Module.End.mul_apply]

example (state : Triple) :
    signedPairing state state =
      signedPairing (tripleDecomposition.Pex state) (tripleDecomposition.Pex state) +
      signedPairing (tripleDecomposition.Pcoex state) (tripleDecomposition.Pcoex state) +
      signedPairing (tripleDecomposition.Pharm state) (tripleDecomposition.Pharm state) :=
  constructed_signed_energy signedPairing tripleSystem tripleSystem.Δ triple_green_inverse
    triple_green_commutes_d triple_green_commutes_cod signedPairing_symmetric
    differential_adjoint state

example : signedPairing (1, 0, 0) (1, 0, 0) = 1 ∧
    signedPairing (0, 0, 1) (0, 0, 1) = -1 := by
  norm_num [signedPairing_apply]

example : signedPairing (2, 3, 5) (2, 3, 5) = 4 + 9 - 25 := by
  norm_num [signedPairing_apply]

example (left right : Triple) :
    signedPairing (tripleDecomposition.Pex left) (tripleDecomposition.Pcoex right) = 0 := by
  have adjoints := constructed_projectors_adjoint signedPairing tripleSystem tripleSystem.Δ
    triple_green_inverse triple_green_commutes_d triple_green_commutes_cod
    signedPairing_symmetric differential_adjoint
  exact orthogonal_projector_images signedPairing tripleDecomposition.Pex tripleDecomposition.Pcoex
    adjoints.1 tripleDecomposition.Pex_Pcoex_zero left right

#print axioms product_green_adjoint
#print axioms orthogonal_projector_images
#print axioms signed_projector_energy
#print axioms constructed_projectors_adjoint
#print axioms constructed_signed_energy
#print axioms KreinGreenEnergy.laplacian_adjoint
#print axioms KreinGreenEnergy.green_adjoint
#print axioms signedPairing_nondegenerate
#print axioms differential_adjoint
#print axioms green_adjoint

end

end InfoGeometry.HodgeCohomology.KreinGreenEnergy.Tests
