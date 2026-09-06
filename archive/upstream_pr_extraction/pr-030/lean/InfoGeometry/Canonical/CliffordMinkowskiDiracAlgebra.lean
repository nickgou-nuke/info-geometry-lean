import Mathlib.Tactic

open Matrix

noncomputable section

namespace InfoGeometry.Canonical.CliffordMinkowskiDiracAlgebra

/-!
# Clifford Algebra Cl(3,1) Dirac Gamma Matrix Algebra & Charge Conjugation

This module formalizes the 4×4 Dirac Gamma matrices $\gamma_0, \gamma_1, \gamma_2, \gamma_3 \in M_4(\mathbb{C})$
in Dirac-Pauli representation, the Clifford algebra anticommutation relations $\{\gamma_\mu, \gamma_\nu\} = 2 \eta_{\mu\nu} I_4$
in Minkowski spacetime signature $(+,-,-,-)$, and the 4D Charge Conjugation operator $\mathcal{C} = i \gamma_2 \gamma_0$:

Proved Theorems:
1. Gamma_0 Square Identity: $\gamma_0^2 = I_4$
2. Gamma_1 Square Identity: $\gamma_1^2 = -I_4$
3. Gamma_2 Square Identity: $\gamma_2^2 = -I_4$
4. Gamma_3 Square Identity: $\gamma_3^2 = -I_4$
5. Gamma_0 and Gamma_1 Anticommutator: $\gamma_0 \gamma_1 + \gamma_1 \gamma_0 = 0$
6. Charge Conjugation Matrix Square: $\mathcal{C}^2 = -I_4$.
-/

abbrev Mat4C := Matrix (Fin 4) (Fin 4) ℂ

/-- Gamma_0 matrix in Dirac-Pauli representation: diag(1, 1, -1, -1). -/
def gamma0 : Mat4C :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Gamma_1 matrix in Dirac-Pauli representation. -/
def gamma1 : Mat4C :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- Gamma_2 matrix in Dirac-Pauli representation. -/
def gamma2 : Mat4C :=
  !![0, 0, 0, -Complex.I;
     0, 0, Complex.I, 0;
     0, Complex.I, 0, 0;
     -Complex.I, 0, 0, 0]

/-- Gamma_3 matrix in Dirac-Pauli representation. -/
def gamma3 : Mat4C :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

/-- Charge conjugation matrix C = i γ₂ γ₀. -/
def chargeConjugation : Mat4C :=
  Complex.I • (gamma2 * gamma0)

/-- **Theorem**: Gamma_0 Square Identity: γ₀² = I₄. -/
theorem gamma0_square : gamma0 * gamma0 = 1 := by
  dsimp [gamma0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- **Theorem**: Gamma_1 Square Identity: γ₁² = -1. -/
theorem gamma1_square : gamma1 * gamma1 = -1 := by
  dsimp [gamma1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- **Theorem**: Gamma_2 Square Identity: γ₂² = -1. -/
theorem gamma2_square : gamma2 * gamma2 = -1 := by
  dsimp [gamma2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- **Theorem**: Gamma_3 Square Identity: γ₃² = -1. -/
theorem gamma3_square : gamma3 * gamma3 = -1 := by
  dsimp [gamma3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

/-- **Theorem**: Gamma_0 and Gamma_1 Anticommutator: γ₀ γ₁ + γ₁ γ₀ = 0. -/
theorem gamma0_gamma1_anticommute : gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  dsimp [gamma0, gamma1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_apply]

/-- **Theorem**: Charge Conjugation Matrix Square: C² = -I₄. -/
theorem charge_conjugation_square : chargeConjugation * chargeConjugation = -1 := by
  dsimp [chargeConjugation, gamma2, gamma0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.CliffordMinkowskiDiracAlgebra
