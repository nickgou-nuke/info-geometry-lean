import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Sandbox: sorry-free replacement for `Canonical/CyclotomicExplicitMatrixBridge`

The companion matrices here are the standard companion matrices of the
cyclotomic polynomials `X^2-X+1` (Phi_6), `X^4+1` (Phi_8), `X^4-X^2+1` (Phi_12)
and `X^8-X^4+1` (Phi_24), together with the tripotent and complex-structure
witnesses.

Every identity is a *finite* identity over `Int`, so each step is discharged by
kernel reduction on explicit integer matrix literals.  Mathlib has no
`CommRing (Matrix n n R)` instance (square-matrix multiplication is genuinely
noncommutative for `n > 1`), so none of the exponents can be collapsed with
`ring`; instead we walk the squaring chain and reuse `pow_mul_eq`.

The 8x8 stage is the only one that would be too large to evaluate in one shot
(`A^24` needs 24 full 8x8 products), so it uses the CAS-generated intermediate
matrices produced by `.agents/sandbox_cyclotomic/gen_cyclotomic_cert.py`.
-/

namespace InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge
namespace Sandbox

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℤ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℤ
abbrev M8 := Matrix (Fin 8) (Fin 8) ℤ

/-! ### Tripotent witness: `diag (1, -1, 0)` -/

def tripotent : M3 := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem tripotent_cube : tripotent ^ 3 = tripotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ### Complex-structure witness: the `2x2` rotation block on a zero padding -/

def complexStage : M3 := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

theorem complexStage_cube : complexStage ^ 3 = -complexStage := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ### `Phi_6 = X^2 - X + 1` -/

def phi6Companion : M2 := !![0, -1; 1, 1]

theorem phi6Companion_order : phi6Companion ^ 6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ### `Phi_8 = X^4 + 1` -/

def phi8Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

theorem phi8Companion_fourth : phi8Companion ^ 4 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem phi8Companion_order : phi8Companion ^ 8 = 1 := by
  calc
    phi8Companion ^ 8 = (phi8Companion ^ 4) ^ 2 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [phi8Companion_fourth]; ext i j; fin_cases i <;> fin_cases j <;> decide

/-! ### `Phi_12 = X^4 - X^2 + 1` -/

def phi12Companion : M4 :=
  !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem phi12Companion_order : phi12Companion ^ 12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ### `Phi_24 = X^8 - X^4 + 1` -/

def phi24Companion : M8 :=
  !![0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- CAS certificate: `A^8 = A^4 - 1`, the defining relation of `Phi_24`. -/
def phi24Companion_eighth : M8 :=
  !![-1, 0, 0, 0, -1, 0, 0, 0;
     0, -1, 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0, -1, 0;
     0, 0, 0, -1, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- CAS certificate: `A^16 = -A^4`. -/
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

end Sandbox
end InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge
