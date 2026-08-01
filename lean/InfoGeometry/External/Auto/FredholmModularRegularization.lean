import Mathlib.Tactic

/-!
# Fredholm/Cayley regularization of modular Delta

The modular operator is regularized near the `s=0` defect by the Cayley/Fredholm
transform

`Δ_reg = (Δ - 1)(Δ + 1)⁻¹`.

For `Δ=e^K`, this is analytically `tanh(K/2)`.  For a biquaternion generator
`K=v σ₁`, the exponential has the form `cosh(v) I + sinh(v) σ₁`, and the
regularized operator is `tanh(v/2) σ₁`.

Lean proves the algebraic matrix core: whenever `c²-s²=1`,

`((cI+sσ)-I) ((cI+sσ)+I)⁻¹ = (s/(c+1)) σ`,

using an explicit inverse.  The analytic identification `s/(c+1)=tanh(v/2)` is
recorded only as a non-formalized external interpretation, for example from
the usual hyperbolic half-angle calculation or an external SymPy check.
-/

noncomputable section

namespace FredholmModularRegularization

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli `σ₁`. -/
def σ1 : M2C := !![0, 1; 1, 0]

/-- Exponential-form modular operator `c I + s σ₁`. -/
def DeltaForm (c s : ℂ) : M2C := c • (1 : M2C) + s • σ1

/-- Numerator `Δ-I`. -/
def cayleyNum (c s : ℂ) : M2C := DeltaForm c s - 1

/-- Denominator `Δ+I`. -/
def cayleyDen (c s : ℂ) : M2C := DeltaForm c s + 1

/-- Explicit inverse of `Δ+I` under `c²-s²=1`: `1/(2(c+1))*((c+1)I-sσ₁)`. -/
def cayleyDenInv (c s : ℂ) : M2C :=
  (1 / (2 * (c + 1))) • ((c + 1) • (1 : M2C) - s • σ1)

/-- The Pauli generator squares to identity. -/
theorem σ1_sq : σ1 * σ1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit denominator inverse is a right inverse when `c²-s²=1`. -/
theorem cayleyDen_mul_inv (c s : ℂ) (h : c^2 - s^2 = 1) (hc : c + 1 ≠ 0) :
    cayleyDen c s * cayleyDenInv c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyDen, cayleyDenInv, DeltaForm, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    field_simp [hc, two_ne_zero] <;>
    ring_nf at h ⊢ <;>
    rw [h] <;> ring

/-- Algebraic Cayley/Fredholm regularization of `cI+sσ₁`. -/
theorem cayley_regularization_pauli (c s : ℂ) (h : c^2 - s^2 = 1) (hc : c + 1 ≠ 0) :
    cayleyNum c s * cayleyDenInv c s = (s / (c + 1)) • σ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyNum, cayleyDenInv, DeltaForm, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    field_simp [hc, two_ne_zero] <;>
    ring_nf at h ⊢ <;>
    rw [h] <;> ring

/-- Scalar Cayley regularization. -/
def scalarReg (δ : ℂ) : ℂ := (δ - 1) / (δ + 1)

/-- The identity modular operator regularizes to zero. -/
theorem scalarReg_one : scalarReg 1 = 0 := by
  norm_num [scalarReg]

end FredholmModularRegularization
