import Mathlib.Tactic

/-!
# Finite Cuntz/Tomita--Takesaki chiral shadow

This module formalizes the finite algebraic core of the requested dictionary from
Cuntz range projectors to Tomita--Takesaki operators.

Because a faithful `O₂` representation by two isometries cannot live literally
inside `2 × 2` matrices, this file uses the theorem-safe finite shadow: the two
orthogonal range projectors `Pplus`, `Pminus` and their parity difference
`eta = Pplus - Pminus`.  The analytic GNS/C*-completion, unbounded modular
operator, and genuine Tomita--Takesaki theorem are not asserted here.

## Closed finite theorems
* `Pplus + Pminus = 1`, orthogonality and idempotence;
* `eta^2 = 1`;
* the two-level modular Hamiltonian
  `K = E₊ Pplus + E₋ Pminus = μ I + δ eta`;
* the hyperbolic polynomial expansion
  `(c I - s eta)(c I + s eta) = I` from `c² - s² = 1`;
* finite matrix formulas for `Δ^{1/2}`, `J`, and
  `S = J Δ^{1/2}`, proving the thermal weights cancel and `S(X)=Xᵀ`.

## Conditional theorems from explicit premises
* The inverse-weight and Tomita-cancellation theorems depend on the named
  premise `c * c - s * s = 1`.

## Scope
This file proves the finite algebraic Cuntz/Tomita shadow stated above.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTomitaTakesaki

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Finite shadow of the left Cuntz range projector `S₁S₁*`. -/
def Pplus : M2R :=
  !![1, 0; 0, 0]

/-- Finite shadow of the right Cuntz range projector `S₂S₂*`. -/
def Pminus : M2R :=
  !![0, 0; 0, 1]

/-- Chiral parity / signature operator `η = P₊ - P₋`. -/
def eta : M2R :=
  Pplus - Pminus

/-- Two-level modular Hamiltonian `K = E₊P₊ + E₋P₋`. -/
def modularHamiltonian (Eplus Eminus : ℝ) : M2R :=
  Eplus • Pplus + Eminus • Pminus

/-- Chemical-potential coordinate. -/
def mu (Eplus Eminus : ℝ) : ℝ :=
  (Eplus + Eminus) / 2

/-- Thermodynamic gap coordinate. -/
def gap (Eplus Eminus : ℝ) : ℝ :=
  (Eplus - Eminus) / 2

/-- Polynomial representative of `exp(-K/2)` after removing the scalar `μI`. -/
def expNegHalf (c s : ℝ) : M2R :=
  c • (1 : M2R) - s • eta

/-- Polynomial representative of `exp(K/2)` after removing the scalar `μI`. -/
def expPosHalf (c s : ℝ) : M2R :=
  c • (1 : M2R) + s • eta

/-- Finite modular half-flow `Δ^{1/2}(X) = e^{-K/2} X e^{K/2}`. -/
def DeltaHalf (c s : ℝ) (X : M2R) : M2R :=
  expNegHalf c s * X * expPosHalf c s

/-- Finite modular conjugation shadow `J(X) = e^{-K/2} Xᵀ e^{K/2}`. -/
def modularJ (c s : ℝ) (X : M2R) : M2R :=
  expNegHalf c s * X.transpose * expPosHalf c s

/-- Finite Tomita shadow `S(X)=J(Δ^{1/2}(X))`. -/
def tomitaS (c s : ℝ) (X : M2R) : M2R :=
  modularJ c s (DeltaHalf c s X)

/-- The two chiral projectors sum to the identity. -/
theorem Pplus_add_Pminus : Pplus + Pminus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pplus, Pminus]

/-- `P₊` is idempotent. -/
theorem Pplus_idempotent : Pplus * Pplus = Pplus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pplus, Matrix.mul_apply]

/-- `P₋` is idempotent. -/
theorem Pminus_idempotent : Pminus * Pminus = Pminus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pminus, Matrix.mul_apply]

/-- The chiral projectors are orthogonal in one order. -/
theorem Pplus_mul_Pminus : Pplus * Pminus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pplus, Pminus, Matrix.mul_apply]

/-- The chiral projectors are orthogonal in the other order. -/
theorem Pminus_mul_Pplus : Pminus * Pplus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pplus, Pminus, Matrix.mul_apply]

/-- The parity matrix is explicitly diagonal. -/
theorem eta_eq_diag : eta = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, Pplus, Pminus]

/-- The chiral parity is involutive: `η² = I`. -/
theorem eta_sq : eta * eta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, Pplus, Pminus, Matrix.mul_apply]

/-- The parity matrix is symmetric. -/
theorem eta_transpose : eta.transpose = eta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, Pplus, Pminus]

/-- The two-level modular Hamiltonian is `μI + δη`. -/
theorem modularHamiltonian_eq_mu_add_gap_eta (Eplus Eminus : ℝ) :
    modularHamiltonian Eplus Eminus =
      mu Eplus Eminus • (1 : M2R) + gap Eplus Eminus • eta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularHamiltonian, mu, gap, eta, Pplus, Pminus] <;> ring

/-- Hyperbolic polynomial inverse relation. -/
theorem expNeg_mul_expPos {c s : ℝ} (h : c * c - s * s = 1) :
    expNegHalf c s * expPosHalf c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expNegHalf, expPosHalf, eta, Pplus, Pminus, Matrix.mul_apply] <;>
    nlinarith [h]

/-- The opposite product is also the identity. -/
theorem expPos_mul_expNeg {c s : ℝ} (h : c * c - s * s = 1) :
    expPosHalf c s * expNegHalf c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expNegHalf, expPosHalf, eta, Pplus, Pminus, Matrix.mul_apply] <;>
    nlinarith [h]

/-- The negative half-flow matrix is symmetric. -/
theorem expNeg_transpose (c s : ℝ) :
    (expNegHalf c s).transpose = expNegHalf c s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expNegHalf, eta, Pplus, Pminus]

/-- The positive half-flow matrix is symmetric. -/
theorem expPos_transpose (c s : ℝ) :
    (expPosHalf c s).transpose = expPosHalf c s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expPosHalf, eta, Pplus, Pminus]

/-- Closed formula for the finite modular half-flow. -/
theorem DeltaHalf_eq (c s : ℝ) (X : M2R) :
    DeltaHalf c s X = expNegHalf c s * X * expPosHalf c s :=
  rfl

/-- Closed formula for finite modular conjugation. -/
theorem modularJ_eq (c s : ℝ) (X : M2R) :
    modularJ c s X = expNegHalf c s * X.transpose * expPosHalf c s :=
  rfl

/--
Finite Tomita cancellation: `S(X)=Xᵀ`.  This is the algebraic cancellation of
the two hyperbolic thermal weights.
-/
theorem tomitaS_eq_transpose {c s : ℝ} (h : c * c - s * s = 1) (X : M2R) :
    tomitaS c s X = X.transpose := by
  calc
    tomitaS c s X
        = expNegHalf c s * (DeltaHalf c s X).transpose * expPosHalf c s := rfl
    _ = expNegHalf c s *
          ((expNegHalf c s * X * expPosHalf c s).transpose) * expPosHalf c s := rfl
    _ = expNegHalf c s *
          (expPosHalf c s * X.transpose * expNegHalf c s) * expPosHalf c s := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, expNeg_transpose, expPos_transpose]
        simp only [mul_assoc]
    _ = (expNegHalf c s * expPosHalf c s) * X.transpose *
          (expNegHalf c s * expPosHalf c s) := by
        simp only [mul_assoc]
    _ = X.transpose := by
        rw [expNeg_mul_expPos h]
        simp

/-- Closed finite packet for the Cuntz/Tomita--Takesaki shadow. -/
theorem cuntz_tomita_takesaki_packet {c s : ℝ} (h : c * c - s * s = 1) :
    Pplus + Pminus = 1 ∧
    eta * eta = 1 ∧
    expNegHalf c s * expPosHalf c s = 1 ∧
    expPosHalf c s * expNegHalf c s = 1 ∧
    (∀ X : M2R, tomitaS c s X = X.transpose) := by
  exact ⟨Pplus_add_Pminus, eta_sq, expNeg_mul_expPos h, expPos_mul_expNeg h,
    tomitaS_eq_transpose h⟩

end InfoGeometry.Canonical.CuntzTomitaTakesaki

end
