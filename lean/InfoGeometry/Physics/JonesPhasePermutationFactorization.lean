/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.JonesPhaseCharacter
import InfoGeometry.Physics.JonesPermutationAction
import InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction

noncomputable section
namespace InfoGeometry.Physics.JonesPhasePermutationFactorization

open B3PresentedGroup JonesPermutationAction JonesPhaseCharacter
open InfoGeometry.External.Auto.TLChain
open InfoGeometry.Topology.ArtinBraidS3Quotient
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction

set_option maxHeartbeats 2000000 in
theorem rho_sigma1 : (rho sigma1 : Matrix (Fin 8) (Fin 8) ℂ) = 1 - e0 := by
  change signMatrix * permutationMatrix sigma1 * signMatrix = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, signedMatrix, signMatrix, permutationMatrix,
      Matrix.permMatrixHom, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Equiv.Perm.permMatrix, Equiv.toPEquiv, PEquiv.toMatrix,
      stateAction, blockAction, stateEquiv, encode, decode, sigma1, e0] <;> decide

set_option maxHeartbeats 2000000 in
theorem rho_sigma2 : (rho sigma2 : Matrix (Fin 8) (Fin 8) ℂ) = 1 - e1 := by
  change signMatrix * permutationMatrix sigma2 * signMatrix = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho, signedMatrix, signMatrix, permutationMatrix,
      Matrix.permMatrixHom, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Equiv.Perm.permMatrix, Equiv.toPEquiv, PEquiv.toMatrix,
      stateAction, blockAction, stateEquiv, encode, decode, sigma2, e1] <;> decide

theorem phaseRemoved_sig0_val :
    (phaseRemoved (PresentedGroup.of B3PresentedGroup.B3Gen.sig0 : B3) :
      Matrix (Fin 8) (Fin 8) ℂ) = 1 - e0 := by
  change (scalarUnit ((phase (PresentedGroup.of B3PresentedGroup.B3Gen.sig0))⁻¹) :
    Matrix (Fin 8) (Fin 8) ℂ) * (phi (PresentedGroup.of B3PresentedGroup.B3Gen.sig0) :
    Matrix (Fin 8) (Fin 8) ℂ) = _
  rw [phase_generator, phi_sig0]
  change algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) (-Complex.I) * JonesBraidB3.s0 = _
  simp [JonesBraidB3.s0, Algebra.algebraMap_eq_smul_one, smul_smul]

theorem phaseRemoved_sig1_val :
    (phaseRemoved (PresentedGroup.of B3PresentedGroup.B3Gen.sig1 : B3) :
      Matrix (Fin 8) (Fin 8) ℂ) = 1 - e1 := by
  change (scalarUnit ((phase (PresentedGroup.of B3PresentedGroup.B3Gen.sig1))⁻¹) :
    Matrix (Fin 8) (Fin 8) ℂ) * (phi (PresentedGroup.of B3PresentedGroup.B3Gen.sig1) :
    Matrix (Fin 8) (Fin 8) ℂ) = _
  rw [phase_generator, phi_sig1]
  change algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) (-Complex.I) * JonesBraidB3.s1 = _
  simp [JonesBraidB3.s1, Algebra.algebraMap_eq_smul_one, smul_smul]

theorem phaseRemoved_eq_permutation : phaseRemoved = rho.comp braidPermutation := by
  apply PresentedGroup.ext
  intro i
  cases i
  · apply Units.ext
    simp only [MonoidHom.comp_apply, braidPermutation_sig0, phaseRemoved_sig0_val, rho_sigma1]
  · apply Units.ext
    simp only [MonoidHom.comp_apply, braidPermutation_sig1, phaseRemoved_sig1_val, rho_sigma2]

theorem jones_phase_permutation_factorization (g : B3) :
    phi g = scalarUnit (phase g) * rho (braidPermutation g) := by
  rw [phase_factorization, phaseRemoved_eq_permutation, MonoidHom.comp_apply]

theorem scalarUnit_injective : Function.Injective scalarUnit := by
  intro z w h
  apply Units.ext
  have he := congrArg (fun u : GL8 => (u : Matrix (Fin 8) (Fin 8) ℂ) 0 0) h
  simpa [scalarUnit, Algebra.algebraMap_eq_smul_one] using he

theorem same_permutation_jones_eq_iff_phase_eq (g h : B3)
    (hp : braidPermutation g = braidPermutation h) :
    phi g = phi h ↔ phase g = phase h := by
  rw [jones_phase_permutation_factorization, jones_phase_permutation_factorization, hp,
    mul_right_cancel_iff]
  exact scalarUnit_injective.eq_iff

end InfoGeometry.Physics.JonesPhasePermutationFactorization
