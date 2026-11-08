/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22ModularWave18

noncomputable section

open scoped Matrix ComplexOrder
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22ModularWave18
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

namespace InfoGeometry.Synthesis.Cl22ModularWave18

private theorem volumeOmega_hermitian_local :
    (castM4 volumeOmega).IsHermitian := by
  rw [volumeOmega_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castM4, RingHom.mapMatrix]

private theorem cast_volumeOmega_commutes_with_reverse_rotor_local (c s : ℝ) :
    Commute (castM4 volumeOmega) (castM4 (andreevRotorRev c s)) := by
  have hJ := cl22_volume_and_bivector_commutation.2.2.1
  have h : volumeOmega * andreevRotorRev c s =
      andreevRotorRev c s * volumeOmega := by
    unfold andreevRotorRev
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, hJ]
    simp only [mul_one, one_mul]
  change (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) =
    (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega)
  rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
    ← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul]
  exact congrArg castM4 h

/-- The finite Gibbs modular automorphism also fixes the reverse-oriented
`Cl(2,2)` Andreev rotor because it commutes with the same volume Hamiltonian. -/
theorem cl22_volume_gibbs_modular_fixes_reverse_rotor
    (β c s : ℝ) :
    gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
        volumeOmega_hermitian_local β (castM4 (andreevRotorRev c s)) =
      castM4 (andreevRotorRev c s) := by
  let H : M4C := castM4 volumeOmega
  let R : M4C := castM4 (andreevRotorRev c s)
  let D := gibbsDensity H volumeOmega_hermitian_local β
  have hHD : Commute H R :=
    cast_volumeOmega_commutes_with_reverse_rotor_local c s
  have hD : Commute D R := by
    unfold D gibbsDensity
    rw [← volumeOmega_hermitian_local.cfc_eq]
    have hsa : IsSelfAdjoint H := volumeOmega_hermitian_local
    exact hsa.commute_cfc hHD (expWeight β)
  rw [gibbsImaginaryTimeAlgEquiv_apply]
  rw [← gibbsDensityUnit_coe (castM4 volumeOmega)
    volumeOmega_hermitian_local β]
  let U := gibbsDensityUnit (castM4 volumeOmega)
    volumeOmega_hermitian_local β
  have hU : Commute (U : M4C) R := by
    simpa [U] using hD
  change (U : M4C) * R * ((U⁻¹ : M4Cˣ) : M4C) = R
  calc
    (U : M4C) * R * ((U⁻¹ : M4Cˣ) : M4C) =
        R * (U : M4C) * ((U⁻¹ : M4Cˣ) : M4C) := by rw [hU.eq]
    _ = R := by
      rw [mul_assoc, Units.mul_inv U, mul_one]

end InfoGeometry.Synthesis.Cl22ModularWave18
