/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.Cl22VolumeGibbsReverseRotorConjugatedKMSWave103
import InfoGeometry.Synthesis.Cl22ModularReverseWave30

noncomputable section

open scoped Matrix ComplexOrder
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22ModularWave18
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

namespace InfoGeometry.Synthesis.Cl22ModularWave18

private theorem reverse_transport_volumeOmega_hermitian :
    (castM4 volumeOmega).IsHermitian := by
  rw [volumeOmega_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castM4, RingHom.mapMatrix]

def cl22_matrix4_e01 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def cl22_matrix4_e10 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem cl22_matrix4_noncommutative :
    cl22_matrix4_e01 * cl22_matrix4_e10 ≠
      cl22_matrix4_e10 * cl22_matrix4_e01 := by
  dsimp
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [cl22_matrix4_e01, cl22_matrix4_e10, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00

/-- The reverse rotor transports the finite Gibbs KMS identity as a whole. -/
theorem cl22_volume_gibbs_reverse_rotor_kms_transport
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    gibbsFunctional (castM4 volumeOmega) reverse_transport_volumeOmega_hermitian β
      (castM4 (andreevRotorRev c s) * (X * Y) *
        castM4 (andreevRotor c s)) =
    gibbsFunctional (castM4 volumeOmega) reverse_transport_volumeOmega_hermitian β
      (castM4 (andreevRotorRev c s) *
        (Y * gibbsImaginaryTimeAlgEquiv
          (castM4 volumeOmega) reverse_transport_volumeOmega_hermitian β X) *
        castM4 (andreevRotor c s)) := by
  have hleft :=
    InfoGeometry.Synthesis.Cl22ModularReverseWave30.cl22_volume_gibbs_reverse_rotor_invariant
      β c s h_norm (X * Y)
  have hright :=
    InfoGeometry.Synthesis.Cl22ModularReverseWave30.cl22_volume_gibbs_reverse_rotor_invariant
      β c s h_norm
      (Y * gibbsImaginaryTimeAlgEquiv
        (castM4 volumeOmega) reverse_transport_volumeOmega_hermitian β X)
  have hkms := gibbsFunctional_kms
    (castM4 volumeOmega) reverse_transport_volumeOmega_hermitian β X Y
  exact hleft.trans (hkms.trans hright.symm)

end InfoGeometry.Synthesis.Cl22ModularWave18

#print axioms InfoGeometry.Synthesis.Cl22ModularWave18.cl22_volume_gibbs_reverse_rotor_kms_transport
