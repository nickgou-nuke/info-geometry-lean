import Mathlib
import InfoGeometryCore.Basic

open InfoGeometryCore
/-!
# U_q(sl(2)) — The Quantum Group (Standard 2×2 Representation)

Chapter 1 of the quantum group → Fibonacci anyon derivation.

The standard 2-dimensional representation of U_q(sl(2)) on ℂ²:

  K = diag(q, q⁻¹)        — Cartan generator (weight)
  E = [[0,1],[0,0]]       — raising operator (creation)
  F = [[0,0],[1,0]]       — lowering operator (annihilation)

satisfying for any q ≠ 0, ±1:
  K·K⁻¹ = K⁻¹·K = I
  K·E·K⁻¹ = q²·E
  K·F·K⁻¹ = q⁻²·F
  [E, F] = (K - K⁻¹)/(q - q⁻¹) = diag(1, -1)

## Connection to Fibonacci

At q = e^{πi/5} (a primitive 10th root of unity):
  q¹⁰ = 1, q⁵ = -1
  q + q⁻¹ = φ = (1+√5)/2  (the golden ratio!)
  [2]_q = q + q⁻¹ = φ     (quantum dimension of spin-1/2)

The representation theory truncates to {1, τ} — the Fibonacci MTC.

## Proved Theorems

1. K·K⁻¹ = I, K⁻¹·K = I
2. K·E·K⁻¹ = q²·E
3. K·F·K⁻¹ = q⁻²·F
4. [E, F] = diag(1, -1) = (K - K⁻¹)/(q - q⁻¹)

Zero axioms. Zero sorries. All matrix computations by fin_cases.
-/

set_option linter.unusedVariables false

open Matrix

noncomputable section

namespace QuantumSl2

/-! ### The Standard 2×2 Matrix Representation -/

/-- Cartan generator: K = diag(q, q⁻¹). -/
def K (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![q, 0; 0, q⁻¹]

/-- Inverse Cartan generator: K⁻¹ = diag(q⁻¹, q). -/
def Kinv (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![q⁻¹, 0; 0, q]

/-- Raising operator: E = [[0,1],[0,0]]. -/
def E : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Lowering operator: F = [[0,0],[1,0]]. -/
def F : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-! ### The U_q(sl(2)) Relations — All Proved -/

/-- K·K⁻¹ = I. -/
theorem K_Kinv_eq_one (q : ℂ) (hq : q ≠ 0) : K q * Kinv q = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K, Kinv, Matrix.mul_apply, hq]

/-- K⁻¹·K = I. -/
theorem Kinv_K_eq_one (q : ℂ) (hq : q ≠ 0) : Kinv q * K q = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K, Kinv, Matrix.mul_apply, hq]

/-- K·E·K⁻¹ = q²·E. -/
theorem K_E_Kinv_eq_qsq_E (q : ℂ) : K q * E * Kinv q = ((q ^ 2) • E) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [K, E, Kinv, Matrix.mul_apply, Matrix.smul_apply, sq]

/-- K·F·K⁻¹ = q⁻²·F. -/
theorem K_F_Kinv_eq_qinv_sq_F (q : ℂ) (hq : q ≠ 0) : K q * F * Kinv q = ((q⁻¹ ^ 2) • F) := by
  ext i j; fin_cases i <;> fin_cases j
  · simp [K, F, Kinv, Matrix.mul_apply, Matrix.smul_apply]
  · simp [K, F, Kinv, Matrix.mul_apply, Matrix.smul_apply]
  · -- (1,0): q⁻¹·q⁻¹ = (q²)⁻¹
    simp [K, F, Kinv, Matrix.mul_apply, Matrix.smul_apply, sq, hq, div_eq_mul_inv]
  · simp [K, F, Kinv, Matrix.mul_apply, Matrix.smul_apply]

/-- The commutator [E, F] = E·F - F·E = diag(1, -1). -/
theorem comm_EF : E * F - F * E = !![(1 : ℂ), 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E, F, Matrix.mul_apply]

/-- (K - K⁻¹)/(q - q⁻¹) = diag(1, -1) when q ≠ q⁻¹ (i.e., q² ≠ 1). -/
theorem K_minus_Kinv_div_q_minus_qinv_eq_diag (q : ℂ) (hq : q ≠ 0) (hq_sq_ne_one : q ^ 2 ≠ 1) :
    ((q - q⁻¹)⁻¹ • (K q - Kinv q)) = !![(1 : ℂ), 0; 0, -1] := by
  have h_denom_ne_zero : q - q⁻¹ ≠ 0 := by
    intro hzero
    have hq_eq_inv : q = q⁻¹ := sub_eq_zero.mp hzero
    have hq_sq_eq_one : q ^ 2 = 1 := by
      calc
        q ^ 2 = q * q := by ring
        _ = q * q⁻¹ := congrArg (fun z => q * z) hq_eq_inv
        _ = 1 := mul_inv_cancel₀ hq
    exact hq_sq_ne_one hq_sq_eq_one
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [K, Kinv, Matrix.smul_apply, h_denom_ne_zero]
  have hq2_sub_ne_zero : q ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hq_sq_ne_one
  have hminus_ne_zero : -1 + q ^ 2 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hq2_sub_ne_zero
  field_simp [h_denom_ne_zero, hminus_ne_zero]
  ring

/-- **The full U_q(sl(2)) relations — all proved**.
    The standard 2×2 representation satisfies all defining relations. -/
theorem standardRep_satisfies_Uqsl2 (q : ℂ) (hq : q ≠ 0) (hq_sq_ne_one : q ^ 2 ≠ 1) :
    K q * Kinv q = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    Kinv q * K q = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    K q * E * Kinv q = ((q ^ 2) • E) ∧
    K q * F * Kinv q = ((q⁻¹ ^ 2) • F) ∧
    E * F - F * E = ((q - q⁻¹)⁻¹ • (K q - Kinv q)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact K_Kinv_eq_one q hq
  · exact Kinv_K_eq_one q hq
  · exact K_E_Kinv_eq_qsq_E q
  · exact K_F_Kinv_eq_qinv_sq_F q hq
  · rw [comm_EF, K_minus_Kinv_div_q_minus_qinv_eq_diag q hq hq_sq_ne_one]

/-! ### The q-Number and Fibonacci Connection -/

/--
The q-number [n]_q = (q^n - q^{-n})/(q - q^{-1}) for q ≠ ±1.
At q = e^{πi/5}: [2]_q = q + q⁻¹ = φ = (1+√5)/2.
-/
def qNumber (q : ℂ) (n : ℤ) (hq_sq_ne_one : q ^ 2 ≠ 1) : ℂ :=
  (q ^ n - q ^ (-n)) / (q - q⁻¹)

/--
The Fibonacci golden ratio φ = (1+√5)/2.
-/
noncomputable abbrev phi := phiC

theorem q_plus_qinv_equals_phi_at_fibonacci :
    (Complex.exp (Real.pi * Complex.I / 5) + Complex.exp (-Real.pi * Complex.I / 5)) = phi := by
  set θ := (Real.pi : ℂ) / 5 with hθ
  have hpos : Complex.exp (Real.pi * Complex.I / 5) = Complex.exp (θ * Complex.I) := by
    dsimp [θ]; ring
  have hneg : Complex.exp (-Real.pi * Complex.I / 5) = Complex.exp (-θ * Complex.I) := by
    dsimp [θ]; ring
  rw [hpos, hneg]
  -- Euler: e^{iθ} + e^{-iθ} = 2*cos(θ)
  rw [Complex.exp_mul_I θ, Complex.exp_mul_I (-θ)]
  simp [Complex.cos_neg, Complex.sin_neg]
  ring_nf
  -- = 2*cos(π/5 : ℂ)
  -- Mathlib: Real.cos(π/5) = (1+√5)/4. Lift to ℂ.
  have hcos : Complex.cos ((Real.pi : ℂ) / 5) = ((1 : ℂ) + (Real.sqrt 5 : ℂ)) / 4 := by
    calc
      Complex.cos ((Real.pi : ℂ) / 5) = (Real.cos (Real.pi / 5) : ℂ) := by
        simpa [div_eq_inv_mul] using (Complex.ofReal_cos (Real.pi / 5)).symm
      _ = ((1 + Real.sqrt 5) / 4 : ℂ) := by
        norm_cast; rw [Real.cos_pi_div_five]
      _ = ((1 : ℂ) + (Real.sqrt 5 : ℂ)) / 4 := by simp
  unfold θ
  rw [hcos]
  -- 2 * ((1 + √5)/4) = (1 + √5)/2 = φ
  unfold phi InfoGeometryCore.phiC
  ring

/--
The Fibonacci fusion rule: τ ⊗ τ = 1 ⊕ τ follows from the truncation
of U_q(sl(2)) representations at q = e^{πi/5}. Only spins j ∈ {0, 1/2}
survive, with quantum dimensions dim(0) = 1, dim(1/2) = φ.

When q¹⁰ = 1 and q⁵ = -1, the quantum dimension [2]_q = φ satisfies
φ² = φ + 1, the defining equation of the golden ratio. The truncated
fusion ring is the Fibonacci anyon model.
**Open debt**: prove the Clebsch-Gordan truncation
V_{1/2} ⊗ V_{1/2} ≅ V₀ ⊕ V_{1/2} in the semisimple quotient.
Status: requires quantum-group representation theory formalization. -/
theorem fibonacci_fusion_from_quantum_group : phi * phi = phi + 1 := by
  unfold phi InfoGeometryCore.phiC
  have h5sq : (Real.sqrt 5 : ℂ) ^ 2 = (5 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (show 0 ≤ 5 by norm_num)
  ring_nf
  rw [h5sq]
  ring_nf

end QuantumSl2
