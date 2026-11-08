/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22ModularReverseWave30
import InfoGeometry.Synthesis.Cl22ReverseRotor

noncomputable section

open scoped Matrix ComplexOrder
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Synthesis.Cl22ModularReverseWave30

namespace InfoGeometry.Synthesis.Cl22ModularReverseClosureWave32

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ

private theorem volumeOmega_commutes_with_rotor (c s : ℝ) :
    volumeOmega * andreevRotor c s = andreevRotor c s * volumeOmega := by
  have hJ := cl22_volume_and_bivector_commutation.2.2.1
  unfold andreevRotor
  rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hJ]
  simp only [mul_one, one_mul]

private theorem cast_volumeOmega_commutes_with_rotor (c s : ℝ) :
    Commute (castM4 volumeOmega) (castM4 (andreevRotor c s)) := by
  change (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotor c s)) =
    (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotor c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega)
  rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
    ← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul]
  exact congrArg castM4 (volumeOmega_commutes_with_rotor c s)

/-- The reverse normalized Andreev rotor fixes the doubled Clifford volume by
conjugation.  This is the opposite orientation of the forward rotor law and
uses the actual `Cl(2,2)` matrix carrier. -/
theorem cl22_volume_reverse_rotor_conjugation
    (c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1) :
    castM4 (andreevRotorRev c s) * castM4 volumeOmega *
        castM4 (andreevRotor c s) = castM4 volumeOmega := by
  have h_rev_rotor :
      castM4 (andreevRotorRev c s) * castM4 (andreevRotor c s) = 1 := by
    change (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) *
        (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotor c s)) = 1
    rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
      andreevRotorRev_mul_andreevRotor c s, h_norm]
    simpa using (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_one
  have hcomm := cast_volumeOmega_commutes_with_rotor c s
  calc
    castM4 (andreevRotorRev c s) * castM4 volumeOmega *
          castM4 (andreevRotor c s) =
        castM4 (andreevRotorRev c s) * castM4 (andreevRotor c s) *
          castM4 volumeOmega := by
            rw [mul_assoc, hcomm.eq, ← mul_assoc]
    _ = castM4 volumeOmega := by rw [h_rev_rotor, one_mul]

end InfoGeometry.Synthesis.Cl22ModularReverseClosureWave32
