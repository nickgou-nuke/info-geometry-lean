import InfoGeometry.Clifford.MonodromyFlowAdapter
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.Tactic

noncomputable section

/-!
# ModularCftBridge

Bridge from the logarithmic-CFT parabolic monodromy block to the standard
`SL(2, Z)` modular generators.  The module keeps the global modular statement
matrix-level: `T` is the unit parabolic shear, and conjugation by `S` moves the
nilpotent shear from the upper to the lower triangular sector.
-/

namespace InfoGeometry.Clifford.ModularCftBridge

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter

/-- The standard modular translation generator `T : τ ↦ τ + 1`. -/
def modularT : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1; 0, 1]

/-- The standard modular inversion generator `S : τ ↦ -1 / τ`. -/
def modularS : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- The inverse of `S`; since `S² = -I`, this is `-S`. -/
def modularSInverse : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

/-- Powers of the standard parabolic generator are additive shears. -/
theorem modularT_pow (m : ℕ) :
    modularT ^ m = !![1, (m : ℂ); 0, 1] := by
  induction m with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [modularT]
  | succ m ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [modularT, Matrix.mul_apply]
      all_goals ring

/-- The LCFT flow with unit parameter is the standard modular `T` generator. -/
theorem modularT_eq_unit_flow :
    modularT = lcftParabolicFlowStep 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularT, lcftParabolicFlowStep, infinitesimalNullGenerator,
      epsilon, jordanNilpotent]

/-- The `m`th modular `T` power is the LCFT parabolic flow at time `m`. -/
theorem modularT_pow_eq_flow (m : ℕ) :
    modularT ^ m = lcftParabolicFlowStep (m : ℂ) := by
  rw [modularT_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lcftParabolicFlowStep, infinitesimalNullGenerator, epsilon,
      jordanNilpotent]

/-- Coordinate form of the LCFT parabolic flow. -/
theorem lcftParabolicFlowStep_eq (t : ℂ) :
    lcftParabolicFlowStep t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lcftParabolicFlowStep, infinitesimalNullGenerator, epsilon,
      jordanNilpotent]

/-- `S` is inverted by `modularSInverse`. -/
theorem modularS_mul_inverse :
    modularS * modularSInverse = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularS, modularSInverse, Matrix.mul_apply]

/-- `modularSInverse` is also a left inverse of `S`. -/
theorem modularS_inverse_mul :
    modularSInverse * modularS = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularS, modularSInverse, Matrix.mul_apply]

/--
Conjugation by `S` moves the logarithmic nilpotent generator from the upper
parabolic sector to the lower parabolic sector.
-/
theorem epsilon_S_conjugation :
    modularS * epsilon * modularSInverse = !![0, 0; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularS, modularSInverse, epsilon, jordanNilpotent, Matrix.mul_apply]

/--
Global modular inversion sends the upper horocycle flow to the lower
horocycle flow, making the logarithmic partner mixing explicit.
-/
theorem parabolicFlow_S_conjugation (t : ℂ) :
    modularS * lcftParabolicFlowStep t * modularSInverse =
      !![1, 0; -t, 1] := by
  rw [lcftParabolicFlowStep_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularS, modularSInverse, Matrix.mul_apply]

/-- The same `S`-conjugation law for the discrete modular `T^m` subgroup. -/
theorem modularT_pow_S_conjugation (m : ℕ) :
    modularS * modularT ^ m * modularSInverse =
      !![1, 0; -(m : ℂ), 1] := by
  rw [modularT_pow_eq_flow]
  exact parabolicFlow_S_conjugation (m : ℂ)

/--
Hadjiivanov monodromy after `m` wraps is a global conformal phase times the
scaled parabolic `T`-sector shear.
-/
theorem monodromy_pow_equals_scaled_modularT (h : ℂ) (m : ℕ) :
    hadjiivanovMonodromy h ^ m =
      lcftPhase h ^ m • !![1, (m : ℂ) * logShearBase; 0, 1] := by
  rw [monodromy_pow_is_compounded_flow]
  simp [lcftParabolicFlowStep_eq]

/--
Corrected algebraic exponential relation for comparing the twist phase at
`τ` and at `1 / τ`.  This is deliberately only an algebraic identity; it does
not assert a false diagonal modular-weight law for logarithmic fields.
-/
theorem phase_algebraic_modular_relation (h τ : ℂ) :
    Complex.exp (-(2 : ℂ) * Complex.I * (Real.pi : ℂ) * h / τ) =
      Complex.exp (-(2 : ℂ) * Complex.I * (Real.pi : ℂ) * h * τ) *
        Complex.exp ((2 : ℂ) * Complex.I * (Real.pi : ℂ) * h * (τ - 1 / τ)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

end InfoGeometry.Clifford.ModularCftBridge
