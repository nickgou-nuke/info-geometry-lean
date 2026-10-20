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

private theorem volumeOmega_hermitian_local :
    (castM4 volumeOmega).IsHermitian := by
  rw [volumeOmega_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castM4, RingHom.mapMatrix]

/-- The finite Gibbs KMS identity descends to normalized rotor-conjugated
observables, with the modular automorphism transported through the rotor. -/
theorem cl22_volume_gibbs_rotor_conjugated_kms
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X Y : M4C) :
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      ((castM4 (andreevRotor c s) * X *
        castM4 (andreevRotorRev c s)) *
        (castM4 (andreevRotor c s) * Y *
          castM4 (andreevRotorRev c s))) =
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) *
        (Y * gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
          volumeOmega_hermitian_local β X) *
        castM4 (andreevRotorRev c s)) := by
  let τ := gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
    volumeOmega_hermitian_local β
  have hrev :
      castM4 (andreevRotorRev c s) * castM4 (andreevRotor c s) = 1 := by
    change (RingHom.mapMatrix (algebraMap ℝ ℂ)
      (andreevRotorRev c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotor c s)) = 1
    rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
      andreevRotorRev_mul_andreevRotor c s, h_norm]
    simpa using (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_one
  have htransport := gibbsFunctional_kms
    (castM4 volumeOmega) volumeOmega_hermitian_local β
    (castM4 (andreevRotor c s) * X *
      castM4 (andreevRotorRev c s))
    (castM4 (andreevRotor c s) * Y *
      castM4 (andreevRotorRev c s))
  have hτ := cl22_volume_gibbs_modular_commutes_with_rotor_conjugation
    (β := β) (c := c) (s := s) X
  change gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      ((castM4 (andreevRotor c s) * X *
        castM4 (andreevRotorRev c s)) *
        (castM4 (andreevRotor c s) * Y *
          castM4 (andreevRotorRev c s))) = _
  rw [htransport]
  change gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      ((castM4 (andreevRotor c s) * Y *
        castM4 (andreevRotorRev c s)) *
        τ (castM4 (andreevRotor c s) * X *
          castM4 (andreevRotorRev c s))) = _
  rw [hτ]
  simp only [mul_assoc]
  rw [← mul_assoc (castM4 (andreevRotorRev c s))
    (castM4 (andreevRotor c s)), hrev, one_mul]

end InfoGeometry.Synthesis.Cl22ModularWave18
