import Mathlib
import proofs.TwoPortScatteringCoefficients

/-!
# Photonic CMT + TMM Backbone

A finite formalization of the proposed hardware dictionary:

* local non-Hermitian coupled-mode theory (CMT) uses the anti-Hermitian
  Hamiltonian `H_eff = -i κ σₓ`;
* the hyperbolic scattering block has `α = κ L`;
* transfer-matrix method (TMM) embeds the local `2 × 2` block into a three-port
  braid skeleton as `T₁(α)` and `T₂(α)`;
* the adjacent Artin words `T₁ T₂ T₁` and `T₂ T₁ T₂` are explicitly defined as
  global chip transfer products.

Caveat: these `3 × 3` nearest-neighbour hyperbolic transfer matrices are the
engineering TMM cascade, not a proof that raw CMT boosts satisfy the Artin/Yang--
Baxter equation.  The nondegenerate Artin relation remains supplied by a
separate two-body R/Majorana construction.
-/

noncomputable section

open Matrix Complex Real

namespace InfoGeometry.GrandUnification.PhotonicCMTTMM

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3R := Matrix (Fin 3) (Fin 3) ℝ

/-- Pauli `σₓ` over `ℂ`. -/
def sigmaX : M2C := !![0, 1; 1, 0]

/-- Effective dissipative CMT coupling strength `α = κ_im L`. -/
def cmtAlpha (kappaIm length : ℝ) : ℝ :=
  kappaIm * length

/-- Anti-Hermitian CMT Hamiltonian `H_eff = -i κ_im σₓ`. -/
def cmtHamiltonian (kappaIm : ℝ) : M2C :=
  (-(kappaIm : ℂ) * Complex.I) • sigmaX

/-- The CMT Hamiltonian is anti-Hermitian: `H† = -H`. -/
theorem cmtHamiltonian_conjTranspose (κ : ℝ) :
    (cmtHamiltonian κ).conjTranspose = - cmtHamiltonian κ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmtHamiltonian, sigmaX]

/-- If `L ≠ 0`, the dissipative coupling needed for target `α` is `κ_im = α/L`. -/
theorem cmtAlpha_div_length {α L : ℝ} (hL : L ≠ 0) :
    cmtAlpha (α / L) L = α := by
  simp [cmtAlpha, div_mul_cancel₀ α hL]

/-- Local hyperbolic two-port scattering block from CMT. -/
def localS (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh α, Real.sinh α; Real.sinh α, Real.cosh α]

/-- Local transmission amplitude. -/
def tCoeff (α : ℝ) : ℝ := Real.cosh α

/-- Local reflection/cross-coupling amplitude. -/
def rCoeff (α : ℝ) : ℝ := Real.sinh α

/-- The local block is exactly `[[t,r],[r,t]]`. -/
theorem localS_eq_coeffs (α : ℝ) :
    localS α = !![tCoeff α, rCoeff α; rCoeff α, tCoeff α] := by
  rfl

/-- `T₁`: three-port TMM embedding coupling ports 1 and 2. -/
def T1 (α : ℝ) : M3R :=
  !![Real.cosh α, Real.sinh α, 0;
     Real.sinh α, Real.cosh α, 0;
     0, 0, 1]

/-- `T₂`: three-port TMM embedding coupling ports 2 and 3. -/
def T2 (α : ℝ) : M3R :=
  !![1, 0, 0;
     0, Real.cosh α, Real.sinh α;
     0, Real.sinh α, Real.cosh α]

/-- Left adjacent Artin-like transfer cascade `T₁ T₂ T₁`. -/
def leftCascade (α : ℝ) : M3R :=
  T1 α * T2 α * T1 α

/-- Right adjacent Artin-like transfer cascade `T₂ T₁ T₂`. -/
def rightCascade (α : ℝ) : M3R :=
  T2 α * T1 α * T2 α

/-- At zero interaction strength, both local TMM generators are identity. -/
theorem T1_zero : T1 0 = (1 : M3R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T1]

/-- At zero interaction strength, both local TMM generators are identity. -/
theorem T2_zero : T2 0 = (1 : M3R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T2]

/-- Consequently the two adjacent cascades agree in the trivial/no-coupling limit. -/
theorem cascades_equal_at_zero : leftCascade 0 = rightCascade 0 := by
  simp [leftCascade, rightCascade, T1_zero, T2_zero]

/-- Explicit first row of the left cascade. -/
theorem leftCascade_row0 (α : ℝ) :
    (leftCascade α) 0 0 = Real.cosh α ^ 2 + Real.cosh α * Real.sinh α ^ 2 ∧
    (leftCascade α) 0 1 = Real.cosh α ^ 2 * Real.sinh α + Real.cosh α * Real.sinh α ∧
    (leftCascade α) 0 2 = Real.sinh α ^ 2 := by
  constructor
  · simp [leftCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  constructor
  · simp [leftCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  · simp [leftCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
    ring

/-- Explicit first row of the right cascade. -/
theorem rightCascade_row0 (α : ℝ) :
    (rightCascade α) 0 0 = Real.cosh α ∧
    (rightCascade α) 0 1 = Real.sinh α * Real.cosh α ∧
    (rightCascade α) 0 2 = Real.sinh α ^ 2 := by
  constructor
  · simp [rightCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
  constructor
  · simp [rightCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [rightCascade, T1, T2, Matrix.mul_apply, Fin.sum_univ_three]
    ring

/-- The TMM cascade definitions are ready for numerical chip simulation. -/
theorem photonic_cmt_tmm_synthesis :
    (∀ κ : ℝ, (cmtHamiltonian κ).conjTranspose = - cmtHamiltonian κ) ∧
    (∀ {α L : ℝ}, L ≠ 0 → cmtAlpha (α / L) L = α) ∧
    T1 0 = (1 : M3R) ∧
    T2 0 = (1 : M3R) ∧
    leftCascade 0 = rightCascade 0 ∧
    (∀ α : ℝ,
      (leftCascade α) 0 0 = Real.cosh α ^ 2 + Real.cosh α * Real.sinh α ^ 2 ∧
      (leftCascade α) 0 1 = Real.cosh α ^ 2 * Real.sinh α + Real.cosh α * Real.sinh α ∧
      (leftCascade α) 0 2 = Real.sinh α ^ 2) := by
  constructor
  · intro κ
    exact cmtHamiltonian_conjTranspose κ
  constructor
  · intro α L hL
    exact cmtAlpha_div_length hL
  constructor
  · exact T1_zero
  constructor
  · exact T2_zero
  constructor
  · exact cascades_equal_at_zero
  · intro α
    exact leftCascade_row0 α

end InfoGeometry.GrandUnification.PhotonicCMTTMM
