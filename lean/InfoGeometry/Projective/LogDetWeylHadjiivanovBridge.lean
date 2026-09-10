import InfoGeometry.Projective.WeylLogScaleBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Logarithmic determinant, Weyl scale, and Jordan monodromy

This owner records the finite algebraic part of the common multiplicative to
additive mechanism.  It deliberately uses the real logarithm only on positive
scalars and does not introduce a global complex logarithm branch.
-/

namespace InfoGeometry.Projective.LogDetWeylHadjiivanovBridge

open InfoGeometry.Projective.WeylLogScaleBridge
open InfoGeometry.Clifford.LogCftMonodromy

abbrev Mat2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- The two-dimensional scalar Weyl dilation. -/
def scalarDilation2 (Ω : ℝ) : Mat2R :=
  !![Ω, 0; 0, Ω]

theorem scalarDilation2_det (Ω : ℝ) :
    (scalarDilation2 Ω).det = Ω ^ 2 := by
  simp [scalarDilation2, Matrix.det_fin_two]
  ring

theorem scalarDilation2_logDet (Ω : ℝ) (hΩ : 0 < Ω) :
    Real.log ((scalarDilation2 Ω).det) = 2 * Real.log Ω := by
  rw [scalarDilation2_det]
  rw [show Ω ^ 2 = Ω * Ω by ring]
  rw [Real.log_mul (ne_of_gt hΩ) (ne_of_gt hΩ)]
  ring

theorem positiveScale_log_add (Ω₁ Ω₂ : PositiveScale) :
    scaleLog ⟨Ω₁.1 * Ω₂.1, mul_pos Ω₁.2 Ω₂.2⟩ =
      scaleLog Ω₁ + scaleLog Ω₂ := by
  exact scaleLog_mul Ω₁ Ω₂

/-- The unipotent Jordan factor has unit determinant. -/
def unipotentJordan (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + c • jordanNilpotent

theorem unipotentJordan_det (c : ℂ) :
    (unipotentJordan c).det = 1 := by
  simp [unipotentJordan, jordanNilpotent, Matrix.det_fin_two]

theorem hadjiivanov_det (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  exact monodromy_is_parabolic h

theorem hadjiivanov_pow_det (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n).det = (lcftPhase h ^ n) ^ 2 := by
  rw [Matrix.det_pow, hadjiivanov_det]
  calc
    (lcftPhase h ^ 2) ^ n = lcftPhase h ^ (2 * n) :=
      (pow_mul (lcftPhase h) 2 n).symm
    _ = lcftPhase h ^ (n * 2) := by rw [Nat.mul_comm]
    _ = (lcftPhase h ^ n) ^ 2 := pow_mul (lcftPhase h) n 2

theorem hadjiivanov_pow_det_unipotent_factor (h : ℂ) (n : ℕ) :
    (hadjiivanovMonodromy h ^ n).det =
      (lcftPhase h ^ n) ^ 2 * (unipotentJordan
        ((n : ℂ) * logShearBase * lcftPhase h ^ n)).det := by
  rw [unipotentJordan_det, mul_one]
  exact hadjiivanov_pow_det h n

end InfoGeometry.Projective.LogDetWeylHadjiivanovBridge
