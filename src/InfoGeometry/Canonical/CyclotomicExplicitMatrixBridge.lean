import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Concrete, representation-neutral matrix witnesses for the low cyclotomic
  stages.  These witnesses are kept separate from the operator-valued spine:
  they do not assert a `G₂` or Clifford interpretation.

  The four companion matrices are the companions of `X^2 - X + 1` (`Phi_6`),
  `X^4 + 1` (`Phi_8`), `X^4 - X^2 + 1` (`Phi_12`) and `X^8 - X^4 + 1`
  (`Phi_24`).  Every identity below is a finite identity over `Int`.

  Mathlib provides `Ring (Matrix n n R)` but deliberately no `CommRing` instance
  (square-matrix multiplication is genuinely noncommutative for `n > 1`), so
  exponents cannot be collapsed with `ring`.  Stages up to `4x4` are discharged
  directly by kernel reduction.  The `8x8` stage would need 24 full matrix
  products in one term, so it walks the squaring chain through the explicit CAS
  certificates `phi24Companion_eighth` and `phi24Companion_sixteenth`, produced
  by `.agents/sandbox_cyclotomic/gen_cyclotomic_cert.py`. -/

namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

abbrev M3 := Matrix (Fin 3) (Fin 3) ℤ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℤ
abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ
abbrev M8 := Matrix (Fin 8) (Fin 8) ℤ

def tripotent : M3 := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem tripotent_cube : tripotent ^ 3 = tripotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def complexStage : M3 := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

theorem complexStage_cube : complexStage ^ 3 = -complexStage := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def phi6Companion : M2 := !![0, -1; 1, 1]

theorem phi6Companion_order : phi6Companion ^ 6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def phi8Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

theorem phi8Companion_fourth : phi8Companion ^ 4 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem phi8Companion_order : phi8Companion ^ 8 = 1 := by
  calc
    phi8Companion ^ 8 = (phi8Companion ^ 4) ^ 2 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
    _ = 1 := by
      rw [phi8Companion_fourth]
      ext i j
      fin_cases i <;> fin_cases j <;> decide

def phi12Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem phi12Companion_order : phi12Companion ^ 12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def phi24Companion : M8 :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- CAS certificate: `phi24Companion ^ 8 = phi24Companion ^ 4 - 1`, the defining
relation of `Phi_24`. -/
def phi24Companion_eighth : M8 :=
  !![-1, 0, 0, 0, -1, 0, 0, 0;
     0, -1, 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0, -1, 0;
     0, 0, 0, -1, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- CAS certificate: `phi24Companion ^ 16 = -phi24Companion ^ 4`. -/
def phi24Companion_sixteenth : M8 :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     -1, 0, 0, 0, -1, 0, 0, 0;
     0, -1, 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0, -1, 0;
     0, 0, 0, -1, 0, 0, 0, -1]

theorem phi24Companion_eighth_eq : phi24Companion ^ 8 = phi24Companion_eighth := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem phi24Companion_sixteenth_eq :
    phi24Companion ^ 16 = phi24Companion_sixteenth := by
  rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul, phi24Companion_eighth_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem phi24Companion_sixteenth_eighth :
    phi24Companion_sixteenth * phi24Companion_eighth = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem phi24Companion_order : phi24Companion ^ 24 = 1 := by
  calc
    phi24Companion ^ 24 = phi24Companion ^ 16 * phi24Companion ^ 8 := by
      rw [show (24 : ℕ) = 16 + 8 by norm_num, pow_add]
    _ = phi24Companion_sixteenth * phi24Companion_eighth := by
      rw [phi24Companion_sixteenth_eq, phi24Companion_eighth_eq]
    _ = 1 := phi24Companion_sixteenth_eighth

end InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge
