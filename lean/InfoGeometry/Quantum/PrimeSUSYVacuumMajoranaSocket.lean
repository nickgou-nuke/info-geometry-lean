/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Quantum.PrimeSUSYVacuum

open Real Finset

/-!
# Prime SUSY Vacuum & Majorana-Polya-Hilbert Socket

Constructive algebraic formalization:
1. Supercharge nilpotency Q² = 0.
2. Anti-commutator {Q, Q†} = H (SUSY algebra).
3. Parity operator grading γ = 1 - 2N = (-1)^N and {γ, Q} = 0.
4. Majorana mode decomposition D = Q + Q† with D² = H.
5. Witten index product formula W(S, β) = ∏_{p ∈ S} (1 - p^(-β)).
6. Boson-fermion cancellation at β = 0: W(S, 0) = 0 for nonempty S.
-/

/-- Matrix representation of a single fermionic mode CAR algebra in 2D. -/
def cAnnihilate : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     0, 0]

def cCreate : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     1, 0]

def numberOp : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     0, 1]

def parityOp : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

def majoranaGamma1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

def majoranaGamma2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1;
     1, 0]

/-! ## 1. Single Mode CAR & SUSY Algebra -/

/-- 🏆 THEOREM 1: Nilpotency of the fermionic creation and annihilation operators. -/
theorem c_annihilate_nilpotent : cAnnihilate * cAnnihilate = 0 := by
  dsimp [cAnnihilate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem c_create_nilpotent : cCreate * cCreate = 0 := by
  dsimp [cCreate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 2: Canonical Anti-Commutation Relation {c, c†} = I₂. -/
theorem car_anticommutation : cAnnihilate * cCreate + cCreate * cAnnihilate = 1 := by
  dsimp [cAnnihilate, cCreate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 3: Number operator representation N = c† c. -/
theorem number_op_eq_create_annihilate : cCreate * cAnnihilate = numberOp := by
  dsimp [cCreate, cAnnihilate, numberOp]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 4: Vacuum projection (1 - N) = c c†. -/
theorem vacuum_proj_eq_annihilate_create : cAnnihilate * cCreate = 1 - numberOp := by
  dsimp [cAnnihilate, cCreate, numberOp]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 5: Parity operator grading γ = 1 - 2N = (-1)^N. -/
theorem parity_op_eq_one_sub_two_number : parityOp = 1 - (2 : ℝ) • numberOp := by
  dsimp [parityOp, numberOp]
  ext i j; fin_cases i <;> fin_cases j <;> (simp <;> ring)

/-- 🏆 THEOREM 6: Parity operator anticommutes with c and c†: {γ, c} = 0, {γ, c†} = 0. -/
theorem parity_anticomm_annihilate : parityOp * cAnnihilate + cAnnihilate * parityOp = 0 := by
  dsimp [parityOp, cAnnihilate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem parity_anticomm_create : parityOp * cCreate + cCreate * parityOp = 0 := by
  dsimp [parityOp, cCreate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ## 2. Majorana Mode Decomposition -/

/-- 🏆 THEOREM 7: Majorana operators γ₁ = c + c†, γ₂ = -c + c†. -/
theorem majorana1_eq_add : majoranaGamma1 = cAnnihilate + cCreate := by
  dsimp [majoranaGamma1, cAnnihilate, cCreate]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 8: Majorana Clifford Algebra: γ₁² = I₂, {γ₁, γ₂} = 0. -/
theorem majorana1_sq : majoranaGamma1 * majoranaGamma1 = 1 := by
  dsimp [majoranaGamma1]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem majorana_anticomm : majoranaGamma1 * majoranaGamma2 + majoranaGamma2 * majoranaGamma1 = 0 := by
  dsimp [majoranaGamma1, majoranaGamma2]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- 🏆 THEOREM 9: Single-mode SUSY Dirac Operator D = ω • γ₁ satisfies D² = ω² • I₂. -/
theorem susy_dirac_sq (omega : ℝ) :
    (omega • majoranaGamma1) * (omega • majoranaGamma1) = (omega ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, majorana1_sq]
  rw [show omega • omega • (1 : Matrix (Fin 2) (Fin 2) ℝ) = (omega * omega) • 1 from smul_smul omega omega 1]
  rw [sq]

/-! ## 3. Finite Prime Register Witten Index & Supersymmetric Cancellation -/

/-- Single prime thermal Witten factor: 1 - p^(-β). -/
noncomputable def primeThermalWittenFactor (p : ℕ) (beta : ℝ) : ℝ :=
  1 - (p : ℝ) ^ (-beta)

/-- Finite prime subsystem Witten index: W(S, β) = ∏_{p ∈ S} (1 - p^(-β)). -/
noncomputable def subsystemThermalWittenIndex (S : Finset ℕ) (beta : ℝ) : ℝ :=
  ∏ p ∈ S, primeThermalWittenFactor p beta

/-- 🏆 THEOREM 10: At β = 0, the single-mode Witten factor vanishes: 1 - p^0 = 1 - 1 = 0. -/
theorem prime_thermal_witten_factor_zero (p : ℕ) (hp : 2 ≤ p) :
    primeThermalWittenFactor p 0 = 0 := by
  unfold primeThermalWittenFactor
  have hp_pos : 0 < (p : ℝ) := by
    have : 2 ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  rw [neg_zero, Real.rpow_zero, sub_self]

/-- 🏆 THEOREM 11: Exact vanishing of the Witten index for any nonempty prime register at β = 0. -/
theorem subsystem_witten_index_zero_of_nonempty (S : Finset ℕ) (p : ℕ) (hp_in : p ∈ S) (hp_prime : 2 ≤ p) :
    subsystemThermalWittenIndex S 0 = 0 := by
  unfold subsystemThermalWittenIndex
  rw [Finset.prod_eq_zero hp_in]
  exact prime_thermal_witten_factor_zero p hp_prime

end PrimeSUSYVacuum
