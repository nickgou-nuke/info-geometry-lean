import InfoGeometry.Canonical.Singular
import InfoGeometry.Canonical.SquareZeroStrainRotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A nonzero Moore–Penrose/Drazin anomaly

The source is an oblique idempotent. Its Moore–Penrose inverse is different
from its Drazin inverse, and its anomaly is a nonzero square-zero shear.
The symmetric and skew parts, multiplied by two, form a normalized split pair.
-/

namespace InfoGeometry.Canonical.AnomalyStrainRotationWitness

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def source : Mat2 := !![1, 1; 0, 0]

def penrose : Mat2 := !![1 / 2, 0; 1 / 2, 0]

def shear : Mat2 := !![0, 1; 0, 0]

/-- The oblique source is idempotent. -/
theorem source_idempotent : source * source = source := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [source, Matrix.mul_apply, Fin.sum_univ_two]

/-- All four actual Moore–Penrose identities hold. -/
theorem source_moorePenrose : IsMoorePenroseInverse source penrose := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [source, penrose, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual Drazin predicate holds at index one with the source as inverse. -/
theorem source_drazin : IsDrazinInverse source source 1 :=
  Drazin.IsDrazinInverse.of_idempotent source_idempotent

/-- The existing Einstein-anomaly definition gives the upper nilpotent corner. -/
theorem source_anomaly : EinsteinAnomaly source penrose source = shear := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [EinsteinAnomaly, source, penrose, shear, Matrix.mul_apply, Fin.sum_univ_two]

/-- These inverse hypotheses admit a nonzero anomaly. -/
theorem source_anomaly_ne_zero : EinsteinAnomaly source penrose source ≠ 0 := by
  rw [source_anomaly]
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [shear] at h01

/-- The spectral projector is genuinely non-self-adjoint in this example. -/
theorem spectral_readout_not_selfAdjoint : star (source * source) ≠ source * source := by
  rw [source_idempotent]
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [source] at h01

/-- The upper corner is square-zero. -/
theorem shear_mul_self_eq_zero : shear * shear = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shear, Matrix.mul_apply, Fin.sum_univ_two]

/-- Twice the strain and rotation give the exact split-Clifford generator laws. -/
theorem normalized_split_pair :
    (shear + star shear) * (shear + star shear) = (1 : Mat2) ∧
    (shear - star shear) * (shear - star shear) = -(1 : Mat2) ∧
    (shear + star shear) * (shear - star shear) =
        -((shear - star shear) * (shear + star shear)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shear, Matrix.mul_apply, Fin.sum_univ_two]
  · exact (SquareZeroStrainRotation.square_zero_star_pair shear shear_mul_self_eq_zero).2

end

end InfoGeometry.Canonical.AnomalyStrainRotationWitness
