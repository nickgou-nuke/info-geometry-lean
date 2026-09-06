import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Dirac-Pauli gamma matrices

Concrete `4 × 4` complex Dirac matrices in the Pauli-Dirac representation:

* `γ⁰ = diag(I₂, -I₂)`;
* `γⁱ = [[0, σᵢ], [-σᵢ, 0]]`;
* `γ⁵ = i γ⁰ γ¹ γ² γ³`.

This is a finite matrix owner for the explicit Pauli embedding.  It is kept
separate from `CrawfordDiracBispinorDensities`, whose gamma matrices are in a
Weyl-basis finite kernel.
-/

namespace InfoGeometry.Clifford.DiracPauliGamma

open scoped Matrix

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Four-component complex Dirac spinor. -/
abbrev DiracSpinor : Type :=
  Fin 4 → ℂ

/-- Four-by-four complex Dirac matrix. -/
abbrev DiracMatrix : Type :=
  Matrix (Fin 4) (Fin 4) ℂ

/-- `γ⁰ = diag(I₂, -I₂)` in the Pauli-Dirac representation. -/
def gamma0 : DiracMatrix :=
  !![(1 : ℂ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- `γ¹ = [[0, σ₁], [-σ₁, 0]]` in the Pauli-Dirac representation. -/
def gamma1 : DiracMatrix :=
  !![(0 : ℂ), 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- `γ² = [[0, σ₂], [-σ₂, 0]]` in the Pauli-Dirac representation. -/
def gamma2 : DiracMatrix :=
  !![(0 : ℂ), 0, 0, -Complex.I;
     0, 0, Complex.I, 0;
     0, Complex.I, 0, 0;
     -Complex.I, 0, 0, 0]

/-- `γ³ = [[0, σ₃], [-σ₃, 0]]` in the Pauli-Dirac representation. -/
def gamma3 : DiracMatrix :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, -1;
     -1, 0, 0, 0;
     0, 1, 0, 0]

/-- `γ⁵ = i γ⁰ γ¹ γ² γ³` in the Pauli-Dirac representation. -/
def gamma5 : DiracMatrix :=
  !![(0 : ℂ), 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Gamma matrices indexed by spacetime coordinate. -/
def gamma : Fin 4 → DiracMatrix
  | 0 => gamma0
  | 1 => gamma1
  | 2 => gamma2
  | 3 => gamma3

/-- Minkowski metric with signature `(+, -, -, -)`. -/
def eta (mu nu : Fin 4) : ℂ :=
  if mu = nu then
    match mu with
    | 0 => 1
    | 1 => -1
    | 2 => -1
    | 3 => -1
  else 0

theorem gamma0_mul_self : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gamma1_mul_self : gamma1 * gamma1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem gamma2_mul_self : gamma2 * gamma2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

theorem gamma3_mul_self : gamma3 * gamma3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

/-! The finite complex structure carried by the spatial `2-3` plane. -/

/-- The bivector `γ²γ³`, viewed as an endomorphism of the Dirac spinor. -/
def gamma23 : DiracMatrix := gamma2 * gamma3

/-- The spatial bivector `γ²γ³` squares to `-1`. -/
theorem gamma23_mul_self : gamma23 * gamma23 = -(1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.neg_apply]

/-- `γ²γ³` commutes with the temporal gamma matrix. -/
theorem gamma23_comm_gamma0 : gamma23 * gamma0 = gamma0 * gamma23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma0, gamma2, gamma3, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- `γ²γ³` commutes with the first spatial gamma matrix. -/
theorem gamma23_comm_gamma1 : gamma23 * gamma1 = gamma1 * gamma23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma1, gamma2, gamma3, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- `γ²γ³` anticommutes with `γ²`. -/
theorem gamma23_anticomm_gamma2 : gamma23 * gamma2 + gamma2 * gamma23 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `γ²γ³` anticommutes with `γ³`. -/
theorem gamma23_anticomm_gamma3 : gamma23 * gamma3 + gamma3 * gamma23 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The spatial bivector preserves the repository's chirality operator. -/
theorem gamma23_comm_gamma5 : gamma23 * gamma5 = gamma5 * gamma23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, gamma5, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-! Finite spectral projectors for the `2-3` complex structure. -/

noncomputable def gamma23ProjectorPlus : DiracMatrix :=
  !![(1 / 2 : ℂ), 1 / 2, 0, 0;
     1 / 2, 1 / 2, 0, 0;
     0, 0, 1 / 2, 1 / 2;
     0, 0, 1 / 2, 1 / 2]

noncomputable def gamma23ProjectorMinus : DiracMatrix :=
  !![(1 / 2 : ℂ), -(1 / 2), 0, 0;
     -(1 / 2), 1 / 2, 0, 0;
     0, 0, 1 / 2, -(1 / 2);
     0, 0, -(1 / 2), 1 / 2]

theorem gamma23ProjectorPlus_idem :
    gamma23ProjectorPlus * gamma23ProjectorPlus = gamma23ProjectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorPlus, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem gamma23ProjectorMinus_idem :
    gamma23ProjectorMinus * gamma23ProjectorMinus = gamma23ProjectorMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorMinus, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem gamma23ProjectorPlus_add_minus :
    gamma23ProjectorPlus + gamma23ProjectorMinus = (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorPlus, gamma23ProjectorMinus, Matrix.one_apply] <;> ring

theorem gamma23ProjectorPlus_mul_minus :
    gamma23ProjectorPlus * gamma23ProjectorMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorPlus, gamma23ProjectorMinus, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem gamma23_mul_projectorPlus :
    gamma23 * gamma23ProjectorPlus = (-Complex.I) • gamma23ProjectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, gamma23ProjectorPlus, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply] <;> ring

theorem gamma23_mul_projectorMinus :
    gamma23 * gamma23ProjectorMinus = Complex.I • gamma23ProjectorMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23, gamma2, gamma3, gamma23ProjectorMinus, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply] <;> ring

theorem gamma23ProjectorPlus_comm_gamma5 :
    gamma23ProjectorPlus * gamma5 = gamma5 * gamma23ProjectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorPlus, gamma5, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem gamma23ProjectorMinus_comm_gamma5 :
    gamma23ProjectorMinus * gamma5 = gamma5 * gamma23ProjectorMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma23ProjectorMinus, gamma5, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem gamma5_eq_i_mul_product :
    Complex.I • (((gamma0 * gamma1) * gamma2) * gamma3) = gamma5 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, gamma1, gamma2, gamma3, gamma5, Matrix.mul_apply, Fin.sum_univ_succ]

theorem gamma5_mul_self : gamma5 * gamma5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma5, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem gamma0_gamma0_anticomm :
    gamma0 * gamma0 + gamma0 * gamma0 = (2 : ℂ) • (1 : DiracMatrix) := by
  rw [gamma0_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring_nf

@[simp] theorem gamma1_gamma1_anticomm :
    gamma1 * gamma1 + gamma1 * gamma1 = (-2 : ℂ) • (1 : DiracMatrix) := by
  rw [gamma1_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring_nf

@[simp] theorem gamma2_gamma2_anticomm :
    gamma2 * gamma2 + gamma2 * gamma2 = (-2 : ℂ) • (1 : DiracMatrix) := by
  rw [gamma2_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring_nf

@[simp] theorem gamma3_gamma3_anticomm :
    gamma3 * gamma3 + gamma3 * gamma3 = (-2 : ℂ) • (1 : DiracMatrix) := by
  rw [gamma3_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring_nf

@[simp] theorem gamma0_gamma1_anticomm : gamma0 * gamma1 + gamma1 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma0, gamma1]

@[simp] theorem gamma0_gamma2_anticomm : gamma0 * gamma2 + gamma2 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma0, gamma2]

@[simp] theorem gamma0_gamma3_anticomm : gamma0 * gamma3 + gamma3 * gamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma0, gamma3]

@[simp] theorem gamma1_gamma2_anticomm : gamma1 * gamma2 + gamma2 * gamma1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma1, gamma2]

@[simp] theorem gamma1_gamma3_anticomm : gamma1 * gamma3 + gamma3 * gamma1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma1, gamma3]

@[simp] theorem gamma2_gamma3_anticomm : gamma2 * gamma3 + gamma3 * gamma2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamma2, gamma3]

@[simp] theorem gamma1_gamma0_anticomm : gamma1 * gamma0 + gamma0 * gamma1 = 0 := by
  simpa [add_comm] using gamma0_gamma1_anticomm

@[simp] theorem gamma2_gamma0_anticomm : gamma2 * gamma0 + gamma0 * gamma2 = 0 := by
  simpa [add_comm] using gamma0_gamma2_anticomm

@[simp] theorem gamma3_gamma0_anticomm : gamma3 * gamma0 + gamma0 * gamma3 = 0 := by
  simpa [add_comm] using gamma0_gamma3_anticomm

@[simp] theorem gamma2_gamma1_anticomm : gamma2 * gamma1 + gamma1 * gamma2 = 0 := by
  simpa [add_comm] using gamma1_gamma2_anticomm

@[simp] theorem gamma3_gamma1_anticomm : gamma3 * gamma1 + gamma1 * gamma3 = 0 := by
  simpa [add_comm] using gamma1_gamma3_anticomm

@[simp] theorem gamma3_gamma2_anticomm : gamma3 * gamma2 + gamma2 * gamma3 = 0 := by
  simpa [add_comm] using gamma2_gamma3_anticomm

/-- Explicit Clifford anticommutation relation `{γᵘ, γᵛ} = 2ηᵘᵛ I₄`. -/
theorem gamma_anticomm (mu nu : Fin 4) :
    gamma mu * gamma nu + gamma nu * gamma mu = (2 * eta mu nu) • (1 : DiracMatrix) := by
  fin_cases mu <;> fin_cases nu <;> simp [gamma, eta]

/-- `γ⁵` anticommutes with all spacetime gamma matrices. -/
theorem gamma5_anticomm (mu : Fin 4) :
    gamma5 * gamma mu + gamma mu * gamma5 = 0 := by
  fin_cases mu <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma, gamma0, gamma1, gamma2, gamma3, gamma5, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.add_apply]

/-- Spinor Lorentz generator with the convention `Σᵘᵛ = (i/4)[γᵘ,γᵛ]`. -/
noncomputable def lorentzGenerator (mu nu : Fin 4) : DiracMatrix :=
  (Complex.I / 4) • (gamma mu * gamma nu - gamma nu * gamma mu)

/--
Commutator normalization for the convention `Σᵘᵛ = (i/4)[γᵘ,γᵛ]`.

With this convention the exact identity is `[γᵘ,γᵛ] = -4i Σᵘᵛ`.
The often-seen `-2i` identity uses the doubled convention
`σᵘᵛ = (i/2)[γᵘ,γᵛ]`.
-/
theorem commutator_eq_neg_four_i_lorentzGenerator (mu nu : Fin 4) :
    gamma mu * gamma nu - gamma nu * gamma mu =
      (-4 * Complex.I) • lorentzGenerator mu nu := by
  unfold lorentzGenerator
  rw [smul_smul]
  have h : (-4 * Complex.I) * (Complex.I / 4) = (1 : ℂ) := by
    rw [div_eq_mul_inv]
    calc
      (-4 * Complex.I) * (Complex.I * (4 : ℂ)⁻¹)
          = -(Complex.I * Complex.I) := by ring
      _ = 1 := by simp [Complex.I_mul_I]
  rw [h, one_smul]

/-! ## Dirac bilinear forms -/

/-- Sesquilinear spinor matrix expectation `ψ† A ψ`. -/
noncomputable def spinorExpectation (A : DiracMatrix) (ψ : DiracSpinor) : ℂ :=
  ∑ i : Fin 4, star (ψ i) * (A.mulVec ψ i)

/-- Dirac scalar bilinear `ψ̄ψ = ψ†γ⁰ψ`. -/
noncomputable def scalarBilinear (ψ : DiracSpinor) : ℂ :=
  spinorExpectation gamma0 ψ

/-- Dirac vector current `ψ̄γᵘψ = ψ†γ⁰γᵘψ`. -/
noncomputable def vectorBilinear (mu : Fin 4) (ψ : DiracSpinor) : ℂ :=
  spinorExpectation (gamma0 * gamma mu) ψ

/-- Dirac bivector/tensor bilinear `ψ̄Σᵘᵛψ = ψ†γ⁰Σᵘᵛψ`. -/
noncomputable def bivectorBilinear (mu nu : Fin 4) (ψ : DiracSpinor) : ℂ :=
  spinorExpectation (gamma0 * lorentzGenerator mu nu) ψ

/-- Dirac pseudoscalar bilinear `ψ̄γ⁵ψ = ψ†γ⁰γ⁵ψ`. -/
noncomputable def pseudoscalarBilinear (ψ : DiracSpinor) : ℂ :=
  spinorExpectation (gamma0 * gamma5) ψ

/-- Dirac axial-vector bilinear `ψ̄γᵘγ⁵ψ = ψ†γ⁰γᵘγ⁵ψ`. -/
noncomputable def axialBilinear (mu : Fin 4) (ψ : DiracSpinor) : ℂ :=
  spinorExpectation (gamma0 * gamma mu * gamma5) ψ

end InfoGeometry.Clifford.DiracPauliGamma
