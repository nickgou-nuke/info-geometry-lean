import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzModularPhaseCharacterBridge
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
import InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge
import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-!
# Cuntz prime phase and the critical-line Euler factor

This owner records the finite local identity carried by an existing Cuntz
modular phase.  For a positive prime label `p`, the phase is the complex power
`p^(it)`.  On `s = 1/2 + iE`, the local Dirichlet weight therefore factors as

`p^(-s) = exp(-(log p)/2) * p^(-iE)`.

The module does not construct an idèle class group, a Galois action, a
Frobenius element, a periodic orbit, or an explicit trace formula.  Those are
separate interfaces or open realization edges in the repository.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CuntzPrimeCriticalEulerFactorBridge

open Complex
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzModularPhaseCharacterBridge
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions

/-- The critical-line local weight written as amplitude times Cuntz phase. -/
def primeCriticalLineWeight (p : ℕ) (E : ℝ) : ℂ :=
  criticalLineWeight (Real.log (p : ℝ)) * modularPhase p (-E)

/-- The corresponding finite local bosonic Euler factor. -/
def primeCriticalEulerFactor (p : ℕ) (E : ℝ) : ℂ :=
  (1 - primeCriticalLineWeight p E)⁻¹

theorem modularPhase_eq_complex_cpow
    (p : ℕ) (hp : p ≠ 0) (t : ℝ) :
    modularPhase p t = (p : ℂ) ^ (Complex.I * (t : ℂ)) := by
  unfold modularPhase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp)]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by exact_mod_cast (Nat.zero_le p))).symm
  rw [hlog]
  congr 1
  ring

theorem modularPhaseUnit_coe_eq_complex_cpow
    (p : ℕ) (hp : p ≠ 0) (t : ℝ) :
    (modularPhaseUnit p t : ℂ) = (p : ℂ) ^ (Complex.I * (t : ℂ)) := by
  rw [modularPhaseUnit_coe, modularPhase_eq_complex_cpow p hp t]

theorem primeCriticalLineWeight_eq_complex_cpow
    (p : ℕ) (hp : p ≠ 0) (E : ℝ) :
    primeCriticalLineWeight p E =
      (p : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * (E : ℂ))) := by
  unfold primeCriticalLineWeight criticalLineWeight modularPhase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp)]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by exact_mod_cast (Nat.zero_le p))).symm
  rw [hlog]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem primeCriticalEulerFactor_readout
    (p : ℕ) (hp : p ≠ 0) (E : ℝ) :
    primeCriticalEulerFactor p E =
      (1 - (p : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * (E : ℂ))))⁻¹ := by
  unfold primeCriticalEulerFactor
  rw [primeCriticalLineWeight_eq_complex_cpow p hp E]

theorem primeCriticalLineWeight_amplitude_phase
    (p : ℕ) (E : ℝ) :
    primeCriticalLineWeight p E =
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) *
        modularPhase p (-E) := by
  rfl

/-- The critical-line weight uses the existing unit-valued modular character. -/
theorem primeCriticalLineWeight_amplitude_character
    (p : ℕ) (E : ℝ) :
    primeCriticalLineWeight p E =
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) *
        (modularPhaseCharacter p (Multiplicative.ofAdd (-E)) : ℂ) := by
  rw [modularPhaseCharacter_coe]
  rfl

/-! ## Dirichlet-shift readout -/

theorem logShift_criticalLine_eigenvalue_amplitude_phase
    (p : ℕ) (hp : 0 < p) (E : ℝ) :
    logShiftOp p
        (expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) =
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) •
        (modularPhase p (-E) •
          expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) := by
  calc
    logShiftOp p
        (expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) =
        ((p : ℂ) ^ (-((1 / 2 : ℂ) + Complex.I * (E : ℂ)))) •
          expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ)) := by
      exact logShift_exponentialEigen_cpow p hp _
    _ = primeCriticalLineWeight p E •
          expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ)) := by
      rw [← primeCriticalLineWeight_eq_complex_cpow p hp.ne' E]
    _ = (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) •
          (modularPhase p (-E) •
            expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) := by
      simp [primeCriticalLineWeight, criticalLineWeight, smul_smul]

/-- The same native shift readout with the unit-valued modular character. -/
theorem logShift_criticalLine_eigenvalue_amplitude_character
    (p : ℕ) (hp : 0 < p) (E : ℝ) :
    logShiftOp p
        (expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) =
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) •
        ((modularPhaseCharacter p (Multiplicative.ofAdd (-E)) : ℂ) •
          expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) := by
  rw [modularPhaseCharacter_coe]
  exact logShift_criticalLine_eigenvalue_amplitude_phase p hp E

/-! ## Finite arithmetic operator readout -/

/-- The finite arithmetic operator inherits the native Cuntz amplitude/phase readout. -/
theorem dirichletOperator_criticalLine_amplitude_character
    (N : ℕ) (a : ℕ → ℂ) (E : ℝ) :
    InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge.dirichletOperator N a
        (expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) =
      (∑ n ∈ Finset.Icc 1 N,
        a n * (Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) : ℂ) *
          (modularPhaseCharacter n (Multiplicative.ofAdd (-E)) : ℂ)) •
        expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ)) := by
  rw [InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge.dirichletOperator_expTestFun]
  apply congrArg (fun z : ℂ => z •
    expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ)))
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hweight :
      Complex.exp (-(((1 / 2 : ℂ) + Complex.I * (E : ℂ)) *
        (Real.log (n : ℝ) : ℂ))) = primeCriticalLineWeight n E := by
    rw [← complexPow_nat_eq_exp_neg_log n hnpos]
    exact (primeCriticalLineWeight_eq_complex_cpow n hnpos.ne' E).symm
  rw [hweight, primeCriticalLineWeight_amplitude_character]
  ring

private lemma criticalLine_half_weight_eq_inv_sqrt
    (p : ℕ) (hp : 0 < p) :
    (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) =
      1 / (Real.sqrt (p : ℝ) : ℂ) := by
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hlog : Real.log (Real.sqrt (p : ℝ)) = Real.log (p : ℝ) / 2 :=
    Real.log_sqrt hpR.le
  calc
    (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) =
        (Real.exp (-Real.log (Real.sqrt (p : ℝ))) : ℂ) := by
      congr 1
      rw [hlog]
      ring_nf
    _ = ((Real.sqrt (p : ℝ))⁻¹ : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hsqrt]
    _ = 1 / (Real.sqrt (p : ℝ) : ℂ) := by
      norm_num [one_div]

/-- The native shift readout with the positive half-weight and modular character. -/
theorem logShift_criticalLine_eigenvalue_half_weight_character
    (p : ℕ) (hp : 0 < p) (E : ℝ) :
    logShiftOp p
        (expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ))) =
      ((1 / (Real.sqrt (p : ℝ) : ℂ)) *
          (modularPhaseCharacter p (Multiplicative.ofAdd (-E)) : ℂ)) •
        expTestFun ((1 / 2 : ℂ) + Complex.I * (E : ℂ)) := by
  rw [logShift_criticalLine_eigenvalue_amplitude_character p hp E]
  rw [criticalLine_half_weight_eq_inv_sqrt p hp]
  simp [smul_smul]

end InfoGeometry.Arithmetic.CuntzPrimeCriticalEulerFactorBridge
