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
    simp [castM4, RingHom.mapMatrix, Matrix.IsHermitian]

/-- The finite Gibbs KMS boundary identity remains valid after transporting both
arguments through a normalized `Cl(2,2)` Andreev rotor conjugation. -/
theorem cl22_volume_gibbs_rotor_kms_transport
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X Y : M4C) :
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) * (X * Y) *
        castM4 (andreevRotorRev c s)) =
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) *
        (Y * gibbsImaginaryTimeAlgEquiv
          (castM4 volumeOmega) volumeOmega_hermitian_local β X) *
        castM4 (andreevRotorRev c s)) := by
  have hleft := cl22_volume_gibbs_rotor_invariant β c s h_norm (X * Y)
  have hright := cl22_volume_gibbs_rotor_invariant β c s h_norm
    (Y * gibbsImaginaryTimeAlgEquiv
      (castM4 volumeOmega) volumeOmega_hermitian_local β X)
  have hkms := gibbsFunctional_kms
    (castM4 volumeOmega) volumeOmega_hermitian_local β X Y
  exact hleft.trans (hkms.trans hright.symm)

/-- The preceding transport is stable under the finite modular automorphism:
its multiplicativity and the KMS boundary law remain true after the same
normalized `Cl(2,2)` rotor conjugation. -/
theorem cl22_volume_gibbs_rotor_modular_kms_transport
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X Y : M4C) :
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) *
        gibbsImaginaryTimeAlgEquiv
          (castM4 volumeOmega) volumeOmega_hermitian_local β (X * Y) *
        castM4 (andreevRotorRev c s)) =
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) *
        (gibbsImaginaryTimeAlgEquiv
            (castM4 volumeOmega) volumeOmega_hermitian_local β Y *
          gibbsImaginaryTimeAlgEquiv
            (castM4 volumeOmega) volumeOmega_hermitian_local β
            (gibbsImaginaryTimeAlgEquiv
              (castM4 volumeOmega) volumeOmega_hermitian_local β X)) *
        castM4 (andreevRotorRev c s)) := by
  let τ := gibbsImaginaryTimeAlgEquiv
    (castM4 volumeOmega) volumeOmega_hermitian_local β
  have hmap : τ (X * Y) = τ X * τ Y := τ.map_mul X Y
  have hkms := gibbsFunctional_kms
    (castM4 volumeOmega) volumeOmega_hermitian_local β (τ X) (τ Y)
  have hleft := cl22_volume_gibbs_rotor_invariant β c s h_norm (τ X * τ Y)
  have hright := cl22_volume_gibbs_rotor_invariant β c s h_norm
    (τ Y * τ (τ X))
  change gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian_local β
      (castM4 (andreevRotor c s) * τ (X * Y) *
        castM4 (andreevRotorRev c s)) = _
  rw [hmap]
  exact hleft.trans (hkms.trans hright.symm)

end InfoGeometry.Synthesis.Cl22ModularWave18
