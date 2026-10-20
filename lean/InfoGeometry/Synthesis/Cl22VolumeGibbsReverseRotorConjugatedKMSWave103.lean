/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.Cl22VolumeGibbsModularRotorConjugationWave79

noncomputable section

open scoped Matrix ComplexOrder
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22ModularWave18
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

namespace InfoGeometry.Synthesis.Cl22ModularWave18

abbrev ReverseM4C := Matrix (Fin 4) (Fin 4) ℂ

private theorem reverse_volumeOmega_hermitian_local :
    (castM4 volumeOmega).IsHermitian := by
  rw [volumeOmega_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castM4, RingHom.mapMatrix]

/-- The finite Gibbs KMS identity for reverse-rotor conjugated observables. -/
theorem cl22_volume_gibbs_reverse_rotor_conjugated_kms
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X Y : ReverseM4C) :
    gibbsFunctional (castM4 volumeOmega) reverse_volumeOmega_hermitian_local β
      ((castM4 (andreevRotorRev c s) * X *
        castM4 (andreevRotor c s)) *
        (castM4 (andreevRotorRev c s) * Y *
          castM4 (andreevRotor c s))) =
    gibbsFunctional (castM4 volumeOmega) reverse_volumeOmega_hermitian_local β
      (castM4 (andreevRotorRev c s) *
        (Y * gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
          reverse_volumeOmega_hermitian_local β X) *
        castM4 (andreevRotor c s)) := by
  let τ := gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
    reverse_volumeOmega_hermitian_local β
  have hmid :
      castM4 (andreevRotor c s) * castM4 (andreevRotorRev c s) = 1 := by
    change (RingHom.mapMatrix (algebraMap ℝ ℂ)
      (andreevRotor c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ)
        (andreevRotorRev c s)) = 1
    rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
      andreevRotor_planar_sheet_rotation c s |>.1, h_norm]
    simp
  have htransport := gibbsFunctional_kms
    (castM4 volumeOmega) reverse_volumeOmega_hermitian_local β
    (castM4 (andreevRotorRev c s) * X * castM4 (andreevRotor c s))
    (castM4 (andreevRotorRev c s) * Y * castM4 (andreevRotor c s))
  have hτ :
      τ (castM4 (andreevRotorRev c s) * X * castM4 (andreevRotor c s)) =
        castM4 (andreevRotorRev c s) * τ X *
          castM4 (andreevRotor c s) := by
    have hRrev : τ (castM4 (andreevRotorRev c s)) =
        castM4 (andreevRotorRev c s) := by
      simpa [τ] using
        (cl22_volume_gibbs_modular_fixes_reverse_rotor β c s)
    have hR : τ (castM4 (andreevRotor c s)) =
        castM4 (andreevRotor c s) := by
      simpa [τ] using (cl22_volume_gibbs_modular_fixes_rotor β c s)
    rw [map_mul τ, map_mul τ, hRrev, hR]
  change gibbsFunctional (castM4 volumeOmega)
      reverse_volumeOmega_hermitian_local β
      ((castM4 (andreevRotorRev c s) * X *
        castM4 (andreevRotor c s)) *
        (castM4 (andreevRotorRev c s) * Y *
          castM4 (andreevRotor c s))) = _
  rw [htransport]
  change gibbsFunctional (castM4 volumeOmega)
      reverse_volumeOmega_hermitian_local β
      ((castM4 (andreevRotorRev c s) * Y *
        castM4 (andreevRotor c s)) *
        τ (castM4 (andreevRotorRev c s) * X *
          castM4 (andreevRotor c s))) = _
  rw [hτ]
  simp only [mul_assoc]
  rw [← mul_assoc (castM4 (andreevRotor c s))
    (castM4 (andreevRotorRev c s)), hmid, one_mul]

end InfoGeometry.Synthesis.Cl22ModularWave18

#print axioms InfoGeometry.Synthesis.Cl22ModularWave18.cl22_volume_gibbs_reverse_rotor_conjugated_kms
