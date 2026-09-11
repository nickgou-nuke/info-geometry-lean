import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Spectral obstruction for a non-trivial Hadjiivanov shear

The logarithmic Jordan block is not normal when its shear is non-zero.  This
owner isolates that finite obstruction; it does not assume a Fibonacci braid
word is unitary and therefore makes no unjustified identification.
-/

namespace InfoGeometry.Canonical

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

def matrixIsNormal (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M * Mᴴ = Mᴴ * M

theorem continuous_upperJordan :
    Continuous (fun p : ℂ × ℂ => upperJordan p.1 p.2) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  fin_cases i <;> fin_cases j
  all_goals
    simp [upperJordan]
    first
    | exact (continuous_fst : Continuous fun p : ℂ × ℂ => p.1)
    | exact (continuous_snd : Continuous fun p : ℂ × ℂ => p.2)
    | exact (continuous_const : Continuous fun p : ℂ × ℂ => (0 : ℂ))

theorem jordanNilpotent_shift_sq (rho kappa : ℂ) :
    (upperJordan rho (rho * kappa) - rho • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ 2 = 0 := by
  have hshift :
      upperJordan rho (rho * kappa) -
          rho • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (rho * kappa) •
          (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperJordan, jordanNilpotent]
  rw [hshift, pow_two, smul_mul_smul, jordanNilpotent_sq]
  simp

theorem upperJordan_not_normal
    {rho kappa : ℂ} (hk : kappa ≠ 0) :
    ¬ matrixIsNormal (upperJordan rho kappa) := by
  intro hnormal
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hnormal
  simp [upperJordan, Matrix.mul_apply,
    Matrix.conjTranspose, Fin.sum_univ_two] at h00
  have hkprod : kappa * (starRingEnd ℂ) kappa = 0 := by
    calc
      kappa * (starRingEnd ℂ) kappa =
          (rho * (starRingEnd ℂ) rho +
            kappa * (starRingEnd ℂ) kappa) -
            rho * (starRingEnd ℂ) rho := by ring
      _ = (starRingEnd ℂ) rho * rho -
            rho * (starRingEnd ℂ) rho := by rw [h00]
      _ = 0 := by ring
  apply hk
  apply Complex.normSq_eq_zero.mp
  have hkcast : (Complex.normSq kappa : ℂ) = 0 := by
    rw [← Complex.mul_conj]
    exact hkprod
  exact_mod_cast hkcast

theorem hadjiivanov_not_normal_of_shear
    {rho kappa : ℂ} (hk : kappa ≠ 0) :
    ¬ matrixIsNormal (upperJordan rho kappa) :=
  upperJordan_not_normal hk

theorem normal_ne_nontrivial_hadjiivanov
    (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : matrixIsNormal W)
    {rho kappa : ℂ} (hk : kappa ≠ 0) :
    W ≠ upperJordan rho kappa := by
  intro hEq
  apply upperJordan_not_normal hk
  simpa [hEq] using hW

theorem equality_implies_zero_hadjiivanov_shear
    (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : matrixIsNormal W)
    (rho kappa : ℂ)
    (hEq : W = upperJordan rho kappa) :
    kappa = 0 := by
  by_contra hk
  exact normal_ne_nontrivial_hadjiivanov W hW hk hEq

end
end InfoGeometry.Canonical
