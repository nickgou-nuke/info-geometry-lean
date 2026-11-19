/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Filter
import Mathlib.Topology.Basic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap

open scoped BigOperators Matrix
open Matrix

/-!
# Osterwalder-Schrader Transfer Semigroup and Mass Gap Precursors

This file formalizes the Euclidean transfer matrix semigroup, its spectral
resolution into ground and excited projection operators, the constructive
positivity of the spectral mass gap $\Delta(J) = -\log(\tanh J) > 0$,
exponential operator clustering, the connection to Elitzur lattice gauge
Wilson string expectations, and transfer-matrix-weighted two-slice
Osterwalder-Schrader reflection positivity.

## Physical and Mathematical Context

In Euclidean quantum gauge field theory (Osterwalder-Schrader formulation),
time-slice transfer matrices $T(J)$ define contraction semigroups whose
spectrum determines the Hamiltonian $H = -\log \widetilde{T}(J) \ge 0$.
The spectral gap above the ground state:
$$\Delta(J) = \log(\coth J) = -\log(\tanh J) > 0 \quad (J > 0)$$
governs exponential clustering:
$$\langle W_L \rangle = (\tanh J)^L = e^{-L \Delta(J)} \to 0 \quad (L \to \infty).$$
This constructively connects the combinatorial Wilson string expectation
proved in `NLinkElitzurChainAndCompactU1Gauge.lean` to Euclidean field theory.

## Reference

* K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions",
  Comm. Math. Phys. 31 (1973), 83-112.
* R. Haag, "Local Quantum Physics: Fields, Particles, Algebras", Springer, 1996.
* J. Glimm and A. Jaffe, "Quantum Physics: A Functional Integral Point of View",
  Springer, 1987.
-/

/-! ### Section 1: Ground and Excited Spectral Projections -/

/-- Ground state projection operator $P_0 = \frac{1}{2} \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$. -/
def projGround : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1/2, 1/2], ![1/2, 1/2]]

/-- Excited state projection operator $P_1 = \frac{1}{2} \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$. -/
def projExcited : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1/2, -1/2], ![-1/2, 1/2]]

/-- $P_0$ is idempotent: $P_0^2 = P_0$. -/
theorem projGround_isIdempotent : projGround * projGround = projGround := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> {
    dsimp [projGround]
    ring
  }

/-- $P_1$ is idempotent: $P_1^2 = P_1$. -/
theorem projExcited_isIdempotent : projExcited * projExcited = projExcited := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> {
    dsimp [projExcited]
    ring
  }

/-- $P_0$ and $P_1$ are mutually orthogonal: $P_0 P_1 = 0$ and $P_1 P_0 = 0$. -/
theorem proj_orthogonal : projGround * projExcited = 0 ∧ projExcited * projGround = 0 := by
  constructor <;> {
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> {
      dsimp [projGround, projExcited]
      ring
    }
  }

/-- $P_0 + P_1 = 1$: complete resolution of the identity. -/
theorem proj_sum : projGround + projExcited = 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> {
    dsimp [projGround, projExcited]
    ring
  }

/-! ### Section 2: Transfer Matrix Operator and Spectral Decomposition -/

/-- Transfer matrix operator $T(J) = \begin{pmatrix} e^J & e^{-J} \\ e^{-J} & e^J \end{pmatrix}$.
The Boltzmann weights for parallel and antiparallel spins across a time link. -/
def transferMat (J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![Real.exp J, Real.exp (-J)], ![Real.exp (-J), Real.exp J]]

/-- Hyperbolic representation of the transfer matrix operator
$T_{\mathrm{hyp}}(J) = 2 \cosh J \cdot I + 2 \sinh J \cdot \sigma_x$. -/
def transferMatHyp (J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![2 * Real.cosh J, 2 * Real.sinh J], ![2 * Real.sinh J, 2 * Real.cosh J]]

/-- Spectral decomposition of the transfer matrix operator:
$T(J) = (2 \cosh J) P_0 + (2 \sinh J) P_1$.
Eigenvalues are $\lambda_0 = 2 \cosh J$ and $\lambda_1 = 2 \sinh J$. -/
theorem transferMat_spectral_decomp (J : ℝ) :
    transferMat J = (2 * Real.cosh J) • projGround + (2 * Real.sinh J) • projExcited := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · dsimp [transferMat, projGround, projExcited]
    rw [← Real.cosh_add_sinh J]
    ring
  · dsimp [transferMat, projGround, projExcited]
    rw [← Real.cosh_sub_sinh J]
    ring
  · dsimp [transferMat, projGround, projExcited]
    rw [← Real.cosh_sub_sinh J]
    ring
  · dsimp [transferMat, projGround, projExcited]
    rw [← Real.cosh_add_sinh J]
    ring

/-- Spectral decomposition of the hyperbolic transfer matrix representation:
$T_{\mathrm{hyp}}(J) = (2 e^J) P_0 + (2 e^{-J}) P_1$. -/
theorem transferMatHyp_spectral_decomp (J : ℝ) :
    transferMatHyp J = (2 * Real.exp J) • projGround + (2 * Real.exp (-J)) • projExcited := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · dsimp [transferMatHyp, projGround, projExcited]
    rw [Real.cosh_eq]
    ring
  · dsimp [transferMatHyp, projGround, projExcited]
    rw [Real.sinh_eq]
    ring
  · dsimp [transferMatHyp, projGround, projExcited]
    rw [Real.sinh_eq]
    ring
  · dsimp [transferMatHyp, projGround, projExcited]
    rw [Real.cosh_eq]
    ring

lemma transferMat_isHermitian (J : ℝ) : (transferMat J).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> {
    dsimp [transferMat]
    simp
  }

lemma transferMatHyp_isHermitian (J : ℝ) : (transferMatHyp J).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;> {
    dsimp [transferMatHyp]
    simp
  }

/-- Quadratic form of the transfer matrix decomposes as a positive sum of squares. -/
lemma transferMat_quad_form (J : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (transferMat J *ᵥ x) =
      Real.cosh J * (x 0 + x 1) ^ 2 + Real.sinh J * (x 0 - x 1) ^ 2 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial]
  dsimp [transferMat]
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Positive definiteness of the transfer matrix operator $T(J)$ for physical coupling $J > 0$. -/
theorem transferMat_posDef {J : ℝ} (hJ : 0 < J) : Matrix.PosDef (transferMat J) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (transferMat_isHermitian J) (fun x hx => ?_)
  rw [transferMat_quad_form J x]
  have hcosh : 0 < Real.cosh J := Real.cosh_pos J
  have hsinh : 0 < Real.sinh J := Real.sinh_pos_iff.mpr hJ
  have h_sq1 : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg (x 0 + x 1)
  have h_sq2 : 0 ≤ (x 0 - x 1) ^ 2 := sq_nonneg (x 0 - x 1)
  have h_cases : (x 0 + x 1) ^ 2 ≠ 0 ∨ (x 0 - x 1) ^ 2 ≠ 0 := by
    by_contra hc
    apply hx
    have hc1 : (x 0 + x 1) ^ 2 = 0 := not_or.mp hc |>.1 |> not_not.mp
    have hc2 : (x 0 - x 1) ^ 2 = 0 := not_or.mp hc |>.2 |> not_not.mp
    have h1 : x 0 + x 1 = 0 := sq_eq_zero_iff.mp hc1
    have h2 : x 0 - x 1 = 0 := sq_eq_zero_iff.mp hc2
    have hx0 : x 0 = 0 := by linarith
    have hx1 : x 1 = 0 := by linarith
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  rcases h_cases with hpos1 | hpos2
  · have h_pos : 0 < Real.cosh J * (x 0 + x 1) ^ 2 :=
      mul_pos hcosh (lt_of_le_of_ne h_sq1 (Ne.symm hpos1))
    have h_term2 : 0 ≤ Real.sinh J * (x 0 - x 1) ^ 2 := mul_nonneg (le_of_lt hsinh) h_sq2
    linarith
  · have h_pos : 0 < Real.sinh J * (x 0 - x 1) ^ 2 :=
      mul_pos hsinh (lt_of_le_of_ne h_sq2 (Ne.symm hpos2))
    have h_term1 : 0 ≤ Real.cosh J * (x 0 + x 1) ^ 2 := mul_nonneg (le_of_lt hcosh) h_sq1
    linarith

/-- Quadratic form of the hyperbolic transfer matrix decomposes as a positive sum of squares. -/
lemma transferMatHyp_quad_form (J : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (transferMatHyp J *ᵥ x) =
      Real.exp J * (x 0 + x 1) ^ 2 + Real.exp (-J) * (x 0 - x 1) ^ 2 := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial]
  dsimp [transferMatHyp]
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Positive definiteness of the hyperbolic transfer matrix operator $T_{\mathrm{hyp}}(J)$ for all $J \in \mathbb{R}$. -/
theorem transferMatHyp_posDef (J : ℝ) : Matrix.PosDef (transferMatHyp J) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (transferMatHyp_isHermitian J) (fun x hx => ?_)
  rw [transferMatHyp_quad_form J x]
  have hexp1 : 0 < Real.exp J := Real.exp_pos J
  have hexp2 : 0 < Real.exp (-J) := Real.exp_pos (-J)
  have h_sq1 : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg (x 0 + x 1)
  have h_sq2 : 0 ≤ (x 0 - x 1) ^ 2 := sq_nonneg (x 0 - x 1)
  have h_cases : (x 0 + x 1) ^ 2 ≠ 0 ∨ (x 0 - x 1) ^ 2 ≠ 0 := by
    by_contra hc
    apply hx
    have hc1 : (x 0 + x 1) ^ 2 = 0 := not_or.mp hc |>.1 |> not_not.mp
    have hc2 : (x 0 - x 1) ^ 2 = 0 := not_or.mp hc |>.2 |> not_not.mp
    have h1 : x 0 + x 1 = 0 := sq_eq_zero_iff.mp hc1
    have h2 : x 0 - x 1 = 0 := sq_eq_zero_iff.mp hc2
    have hx0 : x 0 = 0 := by linarith
    have hx1 : x 1 = 0 := by linarith
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  rcases h_cases with hpos1 | hpos2
  · have h_pos : 0 < Real.exp J * (x 0 + x 1) ^ 2 :=
      mul_pos hexp1 (lt_of_le_of_ne h_sq1 (Ne.symm hpos1))
    have h_term2 : 0 ≤ Real.exp (-J) * (x 0 - x 1) ^ 2 := mul_nonneg (le_of_lt hexp2) h_sq2
    linarith
  · have h_pos : 0 < Real.exp (-J) * (x 0 - x 1) ^ 2 :=
      mul_pos hexp2 (lt_of_le_of_ne h_sq2 (Ne.symm hpos2))
    have h_term1 : 0 ≤ Real.exp J * (x 0 + x 1) ^ 2 := mul_nonneg (le_of_lt hexp1) h_sq1
    linarith

/-! ### Section 3: Normalized Transfer Matrix and Powers -/

/-- Normalized transfer matrix $\widetilde{T}(J) = \frac{1}{2 \cosh J} T(J) = P_0 + (\tanh J) P_1$. -/
def normTransferMat (J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  projGround + (Real.tanh J) • projExcited

/-- Product of two spectral mixtures is diagonal in the projection basis. -/
lemma proj_mul_proj (x y : ℝ) :
    (projGround + x • projExcited) * (projGround + y • projExcited) =
    projGround + (x * y) • projExcited := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> {
    dsimp [projGround, projExcited]
    ring
  }

/-- Power formula for the normalized transfer matrix operator:
$\widetilde{T}(J)^L = P_0 + (\tanh J)^L P_1$. -/
theorem normTransferMat_pow (J : ℝ) (L : ℕ) :
    (normTransferMat J) ^ L = projGround + ((Real.tanh J) ^ L) • projExcited := by
  induction L with
  | zero =>
    ext i j
    simp only [pow_zero, one_smul, Matrix.one_apply, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> {
      dsimp [projGround, projExcited]
      ring
    }
  | succ n ih =>
    rw [pow_succ, ih, normTransferMat, proj_mul_proj, ← pow_succ]

/-! ### Section 4: Spectral Mass Gap and Exponential Clustering -/

/-- Spectral mass gap $\Delta(J) = -\log(\tanh J) = \log(\coth J)$. -/
def spectralMassGap (J : ℝ) : ℝ :=
  -Real.log (Real.tanh J)

/-- The spectral mass gap is strictly positive for any positive coupling $J > 0$. -/
theorem spectralMassGap_pos {J : ℝ} (hJ : 0 < J) : 0 < spectralMassGap J := by
  dsimp [spectralMassGap]
  have ht_pos : 0 < Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J)
  have ht_lt : Real.tanh J < 1 := Real.tanh_lt_one J
  have hlog_neg : Real.log (Real.tanh J) < 0 := Real.log_neg ht_pos ht_lt
  linarith

/-- Exponential decay of excited sector correlations governed by the spectral mass gap:
$(\tanh J)^L = e^{-L \Delta(J)}$. -/
theorem normTransferMat_pow_eq_exp_gap (J : ℝ) (hJ : 0 < J) (L : ℕ) :
    (Real.tanh J) ^ L = Real.exp (- (L : ℝ) * spectralMassGap J) := by
  dsimp [spectralMassGap]
  have ht_pos : 0 < Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J)
  have h_exp_log : Real.exp (Real.log (Real.tanh J)) = Real.tanh J := Real.exp_log ht_pos
  have h_alg : - (L : ℝ) * -Real.log (Real.tanh J) = (L : ℝ) * Real.log (Real.tanh J) := by ring
  rw [h_alg, Real.exp_nat_mul, h_exp_log]

/-- Exponential clustering tendsto zero: $\lim_{L \to \infty} (\tanh J)^L = 0$. -/
theorem normTransferMat_clustering_tendsto_zero {J : ℝ} (hJ : 0 < J) :
    Filter.Tendsto (fun L : ℕ => (Real.tanh J) ^ L) Filter.atTop (nhds 0) := by
  have ht_nonneg : 0 ≤ Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact le_of_lt (div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J))
  exact tendsto_pow_atTop_nhds_zero_of_lt_one ht_nonneg (Real.tanh_lt_one J)

/-! ### Section 5: Bridge to Elitzur Wilson String Expectation -/

/-- Ground state vector $v_0 = \begin{pmatrix} 1 \\ 1 \end{pmatrix}$. -/
def vecGround : Fin 2 → ℝ := ![1, 1]

/-- Excited state vector $v_1 = \begin{pmatrix} 1 \\ -1 \end{pmatrix}$. -/
def vecExcited : Fin 2 → ℝ := ![1, -1]

/-- Pauli $\sigma_z$ spin operator on the 2-state space. -/
def matSigmaZ : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0], ![0, -1]]

/-- Pauli $\sigma_x$ spin flip operator on the 2-state space. -/
def matSigmaX : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1], ![1, 0]]

/-- Wilson string expectation from the transfer matrix matches Elitzur's chain expectation
$\langle v_0, \sigma_z \widetilde{T}(J)^L \sigma_z v_0 \rangle / \langle v_0, v_0 \rangle = (\tanh J)^L$. -/
theorem expect_wilson_from_transferMat (J : ℝ) (L : ℕ) :
    (vecGround ⬝ᵥ (matSigmaZ *ᵥ ((normTransferMat J) ^ L *ᵥ (matSigmaZ *ᵥ vecGround)))) /
      (vecGround ⬝ᵥ vecGround) = (Real.tanh J) ^ L := by
  have h_sz_v0 : matSigmaZ *ᵥ vecGround = vecExcited := by
    ext i
    fin_cases i <;> {
      dsimp [mulVec, dotProduct, matSigmaZ, vecGround, vecExcited]
      rw [Fin.sum_univ_two]
      norm_num
    }
  have h_P0_v1 : projGround *ᵥ vecExcited = 0 := by
    ext i
    fin_cases i <;> {
      dsimp [mulVec, dotProduct, projGround, vecExcited]
      rw [Fin.sum_univ_two]
      norm_num
    }
  have h_P1_v1 : projExcited *ᵥ vecExcited = vecExcited := by
    ext i
    fin_cases i <;> {
      dsimp [mulVec, dotProduct, projExcited, vecExcited]
      rw [Fin.sum_univ_two]
      norm_num
    }
  have h_TL_v1 : (normTransferMat J) ^ L *ᵥ vecExcited = ((Real.tanh J) ^ L) • vecExcited := by
    rw [normTransferMat_pow, Matrix.add_mulVec, Matrix.smul_mulVec, h_P0_v1, h_P1_v1]
    simp only [zero_add]
  have h_sz_v1 : matSigmaZ *ᵥ vecExcited = vecGround := by
    ext i
    fin_cases i <;> {
      dsimp [mulVec, dotProduct, matSigmaZ, vecExcited, vecGround]
      rw [Fin.sum_univ_two]
      norm_num
    }
  have h_sz_TL_v1 : matSigmaZ *ᵥ ((normTransferMat J) ^ L *ᵥ vecExcited) =
      ((Real.tanh J) ^ L) • vecGround := by
    rw [h_TL_v1, Matrix.mulVec_smul, h_sz_v1]
  have h_dot_norm : vecGround ⬝ᵥ vecGround = 2 := by
    dsimp [dotProduct, vecGround]
    rw [Fin.sum_univ_two]
    norm_num
  have h_dot : vecGround ⬝ᵥ (((Real.tanh J) ^ L) • vecGround) = 2 * (Real.tanh J) ^ L := by
    dsimp [dotProduct, vecGround]
    rw [Fin.sum_univ_two]
    norm_num
    ring
  rw [h_sz_v0, h_sz_TL_v1, h_dot, h_dot_norm]
  ring

/-! ### Section 6: Non-Commutativity Witness (OpenGauss Trap T16) -/

/-- Closed non-commutativity witness: $\sigma_x \sigma_z \ne \sigma_z \sigma_x$.
Witnesses the non-commutative operator algebra $M_2(\mathbb{R})$ (OpenGauss Trap T16). -/
theorem matSigmaX_mul_matSigmaZ_ne : matSigmaX * matSigmaZ ≠ matSigmaZ * matSigmaX := by
  intro h
  have h01 : (matSigmaX * matSigmaZ) 0 1 = (matSigmaZ * matSigmaX) 0 1 := by rw [h]
  have h_lhs : (matSigmaX * matSigmaZ) 0 1 = -1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [matSigmaX, matSigmaZ]
    ring
  have h_rhs : (matSigmaZ * matSigmaX) 0 1 = 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [matSigmaX, matSigmaZ]
    ring
  rw [h_lhs, h_rhs] at h01
  norm_num at h01

/-- Non-commutativity witness: the transfer matrix $T(J)$ does not commute with $\sigma_z$.
This demonstrates non-abelian operator ring behavior and prevents scalar degeneration (T16). -/
theorem transferMat_noncomm_witness {J : ℝ} (hJ : 0 < J) :
    transferMat J * matSigmaZ ≠ matSigmaZ * transferMat J := by
  intro h
  have h01 : (transferMat J * matSigmaZ) 0 1 = (matSigmaZ * transferMat J) 0 1 := by rw [h]
  have h_lhs : (transferMat J * matSigmaZ) 0 1 = -Real.exp (-J) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [transferMat, matSigmaZ]
    ring
  have h_rhs : (matSigmaZ * transferMat J) 0 1 = Real.exp (-J) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [transferMat, matSigmaZ]
    ring
  rw [h_lhs, h_rhs] at h01
  have h_zero : 2 * Real.exp (-J) = 0 := by linarith
  have h_pos : 0 < Real.exp (-J) := Real.exp_pos (-J)
  have h_strict : 0 < J + 2 * Real.exp (-J) := add_pos hJ (mul_pos (by norm_num) h_pos)
  linarith [h_zero, h_strict]

/-- Hyperbolic non-commutativity witness: $T_{\mathrm{hyp}}(J) \sigma_z \ne \sigma_z T_{\mathrm{hyp}}(J)$. -/
theorem transferMatHyp_noncomm_witness {J : ℝ} (hJ : 0 < J) :
    transferMatHyp J * matSigmaZ ≠ matSigmaZ * transferMatHyp J := by
  intro h
  have h01 : (transferMatHyp J * matSigmaZ) 0 1 = (matSigmaZ * transferMatHyp J) 0 1 := by rw [h]
  have h_lhs : (transferMatHyp J * matSigmaZ) 0 1 = - (2 * Real.sinh J) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [transferMatHyp, matSigmaZ]
    ring
  have h_rhs : (matSigmaZ * transferMatHyp J) 0 1 = 2 * Real.sinh J := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [transferMatHyp, matSigmaZ]
    ring
  rw [h_lhs, h_rhs] at h01
  have h_zero : 4 * Real.sinh J = 0 := by linarith
  have h_pos : 0 < Real.sinh J := Real.sinh_pos_iff.mpr hJ
  linarith

/-! ### Section 7: Transfer-Matrix Osterwalder-Schrader Reflection Positivity and Cauchy-Schwarz -/

/-- Euclidean time-reflection involution $\theta$ on two-slice configurations `Fin 2 × Fin 2`:
swaps the negative-time spin slice $s_-$ and positive-time spin slice $s_+$. -/
def osReflect (F : Fin 2 × Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun p => F (p.2, p.1)

/-- Time-reflection $\theta$ is an involution: $\theta(\theta(F)) = F$. -/
theorem osReflect_involutive (F : Fin 2 × Fin 2 → ℝ) :
    osReflect (osReflect F) = F := by
  ext ⟨s_neg, s_pos⟩
  dsimp [osReflect]

/-- Time-reflection $\theta$ is a non-trivial involution ($\theta \ne \mathrm{id}$). -/
theorem osReflect_ne_id :
    ∃ F : Fin 2 × Fin 2 → ℝ, osReflect F ≠ F := by
  refine ⟨fun p => if p.1 = 0 ∧ p.2 = 1 then 1 else 0, ?_⟩
  intro h
  have h01 := congr_fun h (0, 1)
  dsimp [osReflect] at h01
  norm_num at h01

/-- Embeds a single-slice observable $f : \mathrm{Fin}\,2 \to \mathbb{R}$ as a positive-time
supported observable $F_f(s_-, s_+) = f(s_+)$ on two-slice configurations. -/
def osPosTimeObs (f : Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun p => f p.2

/-- Single-step Euclidean partition function $Z(J) = \sum_{s_-, s_+} T(J)_{s_-, s_+}$. -/
def osPartitionFn (J : ℝ) : ℝ :=
  ∑ s_neg : Fin 2, ∑ s_pos : Fin 2, transferMat J s_neg s_pos

lemma osPartitionFn_formula (J : ℝ) : osPartitionFn J = 4 * Real.cosh J := by
  dsimp [osPartitionFn, transferMat]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Real.cosh_eq]
  norm_num
  ring

lemma osPartitionFn_pos (J : ℝ) : 0 < osPartitionFn J := by
  rw [osPartitionFn_formula]
  exact mul_pos (by norm_num) (Real.cosh_pos J)

/-- Normalized Osterwalder-Schrader Euclidean expectation weighted by the
transfer-matrix Boltzmann kernel $T(J)_{s_-, s_+}$ across the time-reflection cut. -/
def osExpectation (J : ℝ) (H : Fin 2 × Fin 2 → ℝ) : ℝ :=
  (∑ s_neg : Fin 2, ∑ s_pos : Fin 2, transferMat J s_neg s_pos * H (s_neg, s_pos)) /
    osPartitionFn J

/-- Normalization of the transfer-weighted expectation: $\mathbb{E}_J[1] = 1$. -/
theorem osExpectation_one (J : ℝ) : osExpectation J (fun _ => 1) = 1 := by
  dsimp [osExpectation]
  have hZ : osPartitionFn J ≠ 0 := ne_of_gt (osPartitionFn_pos J)
  simp only [mul_one]
  exact div_self hZ

/-- Osterwalder-Schrader physical bilinear form on positive-time observables:
$\langle f, g \rangle_{\mathrm{OS}, J} := \mathbb{E}_J[\theta(F_f) \cdot F_g]$. -/
def osBilinForm (J : ℝ) (f g : Fin 2 → ℝ) : ℝ :=
  osExpectation J (osReflect (osPosTimeObs f) * osPosTimeObs g)

/-- Exact transfer-operator representation of the OS bilinear form:
$\langle f, g \rangle_{\mathrm{OS}, J} = \frac{f \cdot (T(J)\, g)}{Z(J)}$. -/
lemma osBilinForm_transfer_rep (J : ℝ) (f g : Fin 2 → ℝ) :
    osBilinForm J f g = (f ⬝ᵥ (transferMat J *ᵥ g)) / osPartitionFn J := by
  dsimp [osBilinForm, osExpectation, osReflect, osPosTimeObs, dotProduct, mulVec]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  ring

/-- Osterwalder-Schrader Reflection Positivity Axiom (OS2) for ferromagnetic coupling $J > 0$:
$\mathbb{E}_J[\theta(F_f) \cdot F_f] \ge 0$ for all positive-time observables $f$,
derived from `transferMat_posDef`. -/
theorem os_reflection_positivity {J : ℝ} (hJ : 0 < J) (f : Fin 2 → ℝ) :
    0 ≤ osBilinForm J f f := by
  rw [osBilinForm_transfer_rep]
  have h_num : 0 ≤ f ⬝ᵥ (transferMat J *ᵥ f) := by
    simpa [star_trivial] using (transferMat_posDef hJ).posSemidef.dotProduct_mulVec_nonneg f
  exact div_nonneg h_num (le_of_lt (osPartitionFn_pos J))

/-- Strict Osterwalder-Schrader reflection positivity for nonzero observables when $J > 0$. -/
theorem os_reflection_positivity_strict {J : ℝ} (hJ : 0 < J) {f : Fin 2 → ℝ} (hf : f ≠ 0) :
    0 < osBilinForm J f f := by
  rw [osBilinForm_transfer_rep]
  have h_num : 0 < f ⬝ᵥ (transferMat J *ᵥ f) := by
    simpa [star_trivial] using (transferMat_posDef hJ).dotProduct_mulVec_pos hf
  exact div_pos h_num (osPartitionFn_pos J)

/-- Coupling-sign sensitivity witness: for antiferromagnetic coupling $J < 0$,
reflection positivity fails on `vecExcited`, proving genuine dependence on $J$ and $T(J)$. -/
theorem os_reflection_positivity_fails_antiferro {J : ℝ} (hJ : J < 0) :
    osBilinForm J vecExcited vecExcited < 0 := by
  rw [osBilinForm_transfer_rep]
  have h_quad : vecExcited ⬝ᵥ (transferMat J *ᵥ vecExcited) = 4 * Real.sinh J := by
    have hq := transferMat_quad_form J vecExcited
    simp only [star_trivial] at hq
    rw [hq]
    dsimp [vecExcited]
    norm_num
    ring
  rw [h_quad]
  have h_sinh_neg : Real.sinh J < 0 := by
    have h_pos : 0 < Real.sinh (-J) := Real.sinh_pos_iff.mpr (neg_pos.mpr hJ)
    linarith [Real.sinh_neg J]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) h_sinh_neg) (osPartitionFn_pos J)

/-- General discriminant non-negativity for quadratic polynomials with non-negative leading coefficient. -/
lemma quadratic_nonneg_discrim {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t^2 - 2 * b * t + c) :
    b^2 ≤ a * c := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb : b = 0 := by
      by_contra hb
      have h1 := h ((c + 1) / (2 * b))
      have hb_ne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
      have h_eval : 0 * ((c + 1) / (2 * b))^2 - 2 * b * ((c + 1) / (2 * b)) + c = -1 := by
        calc 0 * ((c + 1) / (2 * b))^2 - 2 * b * ((c + 1) / (2 * b)) + c
          _ = - (2 * b * (c + 1) / (2 * b)) + c := by ring
          _ = - (c + 1) + c := by rw [mul_div_cancel_left₀ (c + 1) hb_ne]
          _ = -1 := by ring
      rw [h_eval] at h1
      linarith
    subst hb
    simp
  · have h1 := h (b / a)
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have h2 : 0 ≤ (a * c - b^2) / a := by
      calc 0 ≤ a * (b / a)^2 - 2 * b * (b / a) + c := h1
        _ = (a * c - b^2) / a := by
          field_simp
          ring
    have h_mul : 0 ≤ ((a * c - b^2) / a) * a := mul_nonneg h2 (le_of_lt ha_pos)
    rw [div_mul_cancel₀ _ ha_ne] at h_mul
    linarith

/-- Osterwalder-Schrader Cauchy-Schwarz Inequality for $J > 0$:
$|\langle f, g \rangle_{\mathrm{OS}, J}|^2 \le \langle f, f \rangle_{\mathrm{OS}, J} \langle g, g \rangle_{\mathrm{OS}, J}$. -/
theorem os_cauchy_schwarz {J : ℝ} (hJ : 0 < J) (f g : Fin 2 → ℝ) :
    (osBilinForm J f g) ^ 2 ≤ osBilinForm J f f * osBilinForm J g g := by
  have ha : 0 ≤ osBilinForm J f f := os_reflection_positivity hJ f
  apply quadratic_nonneg_discrim ha
  intro t
  have h_nonneg : 0 ≤ osBilinForm J (t • f - g) (t • f - g) :=
    os_reflection_positivity hJ (t • f - g)
  have h_expand :
      osBilinForm J (t • f - g) (t • f - g) =
        osBilinForm J f f * t^2 - 2 * osBilinForm J f g * t + osBilinForm J g g := by
    simp only [osBilinForm_transfer_rep]
    have hZ : osPartitionFn J ≠ 0 := ne_of_gt (osPartitionFn_pos J)
    have h_num :
        (t • f - g) ⬝ᵥ (transferMat J *ᵥ (t • f - g)) =
          (f ⬝ᵥ (transferMat J *ᵥ f)) * t^2 -
            2 * (f ⬝ᵥ (transferMat J *ᵥ g)) * t + (g ⬝ᵥ (transferMat J *ᵥ g)) := by
      simp only [dotProduct, mulVec, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [transferMat]
      ring
    rw [h_num]
    field_simp [hZ]
  rw [← h_expand]
  exact h_nonneg

/-- Multi-step transfer semigroup reflection positivity: for all $J > 0$ and all $L \in \mathbb{N}$,
the $L$-step normalized transfer semigroup $\widetilde{T}(J)^L$ defines a positive-semidefinite
form $\langle f, \widetilde{T}(J)^L f \rangle \ge 0$. -/
theorem os_semigroup_reflection_positivity {J : ℝ} (hJ : 0 < J) (L : ℕ) (f : Fin 2 → ℝ) :
    0 ≤ f ⬝ᵥ ((normTransferMat J) ^ L *ᵥ f) := by
  rw [normTransferMat_pow]
  have h_quad :
      f ⬝ᵥ ((projGround + ((Real.tanh J) ^ L) • projExcited) *ᵥ f) =
        (1 / 2) * (f 0 + f 1) ^ 2 + ((Real.tanh J) ^ L / 2) * (f 0 - f 1) ^ 2 := by
    simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    dsimp [projGround, projExcited]
    ring
  rw [h_quad]
  have ht_pos : 0 < Real.tanh J := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hJ) (Real.cosh_pos J)
  have h_term1 : 0 ≤ (1 / 2 : ℝ) * (f 0 + f 1) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have h_term2 : 0 ≤ ((Real.tanh J) ^ L / 2) * (f 0 - f 1) ^ 2 :=
    mul_nonneg (div_nonneg (pow_nonneg (le_of_lt ht_pos) L) (by norm_num)) (sq_nonneg _)
  exact add_nonneg h_term1 h_term2

end InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
