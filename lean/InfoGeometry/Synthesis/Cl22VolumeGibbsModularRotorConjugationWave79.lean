/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22VolumeGibbsModularFixesRotorWave77
import InfoGeometry.Synthesis.Cl22VolumeGibbsModularFixesReverseRotorWave78

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

/-- The finite Gibbs modular automorphism commutes with conjugation by the
normalized `Cl(2,2)` Andreev rotor. -/
theorem cl22_volume_gibbs_modular_commutes_with_rotor_conjugation
    (β c s : ℝ) (X : M4C) :
    gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
        volumeOmega_hermitian_local β
        (castM4 (andreevRotor c s) * X *
          castM4 (andreevRotorRev c s)) =
      castM4 (andreevRotor c s) *
        gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
          volumeOmega_hermitian_local β X *
        castM4 (andreevRotorRev c s) := by
  let τ := gibbsImaginaryTimeAlgEquiv (castM4 volumeOmega)
    volumeOmega_hermitian_local β
  have hR : τ (castM4 (andreevRotor c s)) =
      castM4 (andreevRotor c s) := by
    simpa [τ] using
      (cl22_volume_gibbs_modular_fixes_rotor β c s)
  have hRrev : τ (castM4 (andreevRotorRev c s)) =
      castM4 (andreevRotorRev c s) := by
    simpa [τ] using
      (cl22_volume_gibbs_modular_fixes_reverse_rotor β c s)
  change τ ((castM4 (andreevRotor c s) * X) *
    castM4 (andreevRotorRev c s)) = _
  rw [map_mul τ, map_mul τ, hR, hRrev]

end InfoGeometry.Synthesis.Cl22ModularWave18
