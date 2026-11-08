/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl22RealDiracCarrier
import InfoGeometry.Canonical.Cl22GibbsConjugationClosureWave24

noncomputable section

open scoped Matrix ComplexOrder
open Matrix
open InfoGeometry.Synthesis.Cl22RealDiracCarrier
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

namespace InfoGeometry.Synthesis.Cl22ModularReverseWave30

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ

noncomputable def castM4 (A : Matrix (Fin 4) (Fin 4) ℝ) : M4C :=
  RingHom.mapMatrix (algebraMap ℝ ℂ) A

private theorem volumeOmega_hermitian :
    (castM4 volumeOmega).IsHermitian := by
  rw [volumeOmega_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [castM4, RingHom.mapMatrix, Matrix.IsHermitian]

private theorem reverse_rotor_right_inverse (c s : ℝ)
    (h_norm : c ^ 2 + s ^ 2 = 1) :
    castM4 (andreevRotor c s) * castM4 (andreevRotorRev c s) = 1 := by
  change (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotor c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) = 1
  rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
    andreevRotor_planar_sheet_rotation c s |>.1, h_norm]
  simpa using (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_one

private theorem volumeOmega_commutes_with_reverse_rotor (c s : ℝ) :
    volumeOmega * andreevRotorRev c s = andreevRotorRev c s * volumeOmega := by
  have hJ := cl22_volume_and_bivector_commutation.2.2.1
  unfold andreevRotorRev
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hJ]
  simp only [mul_one, one_mul]

private theorem cast_volumeOmega_commutes_with_reverse_rotor (c s : ℝ) :
    Commute (castM4 volumeOmega) (castM4 (andreevRotorRev c s)) := by
  change (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) =
    (RingHom.mapMatrix (algebraMap ℝ ℂ) (andreevRotorRev c s)) *
      (RingHom.mapMatrix (algebraMap ℝ ℂ) volumeOmega)
  rw [← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul,
    ← (RingHom.mapMatrix (algebraMap ℝ ℂ)).map_mul]
  exact congrArg castM4 (volumeOmega_commutes_with_reverse_rotor c s)

/-- The finite `Cl(2,2)` Gibbs functional is invariant under the reverse
orientation of every normalized Andreev rotor. -/
theorem cl22_volume_gibbs_reverse_rotor_invariant
    (β c s : ℝ) (h_norm : c ^ 2 + s ^ 2 = 1)
    (X : M4C) :
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian β
      (castM4 (andreevRotorRev c s) * X * castM4 (andreevRotor c s)) =
    gibbsFunctional (castM4 volumeOmega) volumeOmega_hermitian β X := by
  exact gibbsFunctional_rightInverse_conjugation_invariant_of_commute
    (castM4 volumeOmega) volumeOmega_hermitian β
    (castM4 (andreevRotorRev c s)) (castM4 (andreevRotor c s)) X
    (reverse_rotor_right_inverse c s h_norm)
    (cast_volumeOmega_commutes_with_reverse_rotor c s)

end InfoGeometry.Synthesis.Cl22ModularReverseWave30
