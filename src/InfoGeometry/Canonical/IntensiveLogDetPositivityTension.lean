/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import InfoGeometry.Analysis.PositiveMatrixDikin
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.HodgeKernel
import InfoGeometry.Physics.NuclearAlgebraicResolventObstruction
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.Canonical.IntensiveLogDetPositivityTension
Role: Canonical formalization of the Intensive Information Geometry vs. Uniform
  Positivity boundary, Dimension-Independent Operator-Norm Cubic Estimate,
  Peirce-Hodge Centralizer-vs-Annihilator Separation & Homotopy Identity, and
  Factorial-Weighted Fock Adjoint & Coherent Shifted-Oscillator Resolution of
  the Nuclear Resolvent Obstruction:
  (1) Intensive potential `F_d(A) = -d⁻¹ log |det A|` and its native 2nd and 3rd
      directional derivatives along `A + s • H`,
  (2) Rank-one projection counterexample: `D²F_d(I)[-2P, -2P] = 4 / d → 0` while
      `I - 2P` has negative quadratic form `< 0` (`¬ PosSemidef (I - 2P)`), and
      the self-concordance ratio blow-up `|D³F_d(I)[P,P,P]|² = 4 d (D²F_d(I)[P,P])³`,
  (3) Dimension-independent hybrid estimate:
      `|traceCubic P H| ≤ ‖normalizedVariation P H‖ * traceQuadratic P H` and
      `|D³F_d(P)[H,H,H]| ≤ 2 ‖P⁻¹/² H P⁻¹/²‖_op D²F_d(P)[H,H]`,
  (4) Peirce-Hodge centralizer vs. four-annihilator separation (`[Q, I] = 0` while
      `I ∉ ker Δ_Q` for `Q ≠ 0`) and exact algebraic homotopy identity,
  (5) Factorial-weighted Fock inner product making `(a† c)_{n+1} = c_n` and
      `(a d)_n = (n+1) d_{n+1}` exact adjoints, and summability of the shifted
      oscillator ground state `E₀ = -g²/ω` (`c_n = (-g/ω)^n / n!`).
===============================================================================
-/

noncomputable section

namespace InfoGeometry.Canonical.IntensiveLogDetPositivityTension

open Matrix Filter Topology
open scoped Matrix BigOperators CStarAlgebra MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
open InfoGeometry.OperatorAlgebra.PeirceSuperoperators
open InfoGeometry.Core.JordanMultiplicationClosure

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-! ===========================================================================
    Section 1: Intensive (Dimension-Normalized) Log-Determinant Potential &
    Native Directional Derivatives
    =========================================================================== -/

/-- The intensive (dimension-normalized) negative log-determinant potential
`F_d(A) = -d⁻¹ log ‖det A‖` on `n × n` complex matrices (`d = Fintype.card n`). -/
def intensiveNegLogDet (n : Type*) [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * negLogDet A

/-- The intensive quadratic trace form `d⁻¹ Re Tr((P⁻¹ H)²)`. -/
def intensiveTraceQuadratic (n : Type*) [Fintype n] [DecidableEq n] (P H : Matrix n n ℂ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * traceQuadratic P H

/-- The intensive cubic trace form `d⁻¹ Re Tr((P⁻¹ H)³)`. -/
def intensiveTraceCubic (n : Type*) [Fintype n] [DecidableEq n] (P H : Matrix n n ℂ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * traceCubic P H

/-- First directional derivative of `intensiveNegLogDet` along `A + s • H`. -/
theorem hasDerivAt_intensiveNegLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (fun s : ℝ => intensiveNegLogDet n (A + s • H))
      ((Fintype.card n : ℝ)⁻¹ * (-(Matrix.trace ((A + t • H)⁻¹ * H)).re)) t := by
  unfold intensiveNegLogDet
  exact (hasDerivAt_negLogDet_add_smul A H hunit).const_mul (Fintype.card n : ℝ)⁻¹

/-- Derivative of the first directional derivative of `intensiveNegLogDet` along `A + s • H`. -/
theorem hasDerivAt_deriv_intensiveNegLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H)))
      ((Fintype.card n : ℝ)⁻¹ * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 2)).re) t := by
  have hraw := (hasDerivAt_deriv_negLogDet_add_smul A H hunit).const_mul (Fintype.card n : ℝ)⁻¹
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_add_smul A H hunit] with s hs
  rw [(hasDerivAt_intensiveNegLogDet_add_smul A H hs).deriv,
    (hasDerivAt_negLogDet_add_smul A H hs).deriv]

/-- Second directional derivative of `intensiveNegLogDet` along `A + s • H`. -/
theorem second_deriv_intensiveNegLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    deriv (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H))) t =
      (Fintype.card n : ℝ)⁻¹ * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 2)).re :=
  (hasDerivAt_deriv_intensiveNegLogDet_add_smul A H hunit).deriv

/-- Second directional derivative of `intensiveNegLogDet` at `t = 0` equals
`intensiveTraceQuadratic n A H`. -/
theorem second_deriv_intensiveNegLogDet_add_smul_zero (A H : Mat) (hA : IsUnit A) :
    deriv (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H))) 0 =
      intensiveTraceQuadratic n A H := by
  simpa [intensiveTraceQuadratic, traceQuadratic, reTrace] using
    second_deriv_intensiveNegLogDet_add_smul A H (t := 0) (by simpa using hA)

/-- Derivative of the second directional derivative of `intensiveNegLogDet` along `A + s • H`. -/
theorem hasDerivAt_second_deriv_intensiveNegLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    HasDerivAt (deriv (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H))))
      ((Fintype.card n : ℝ)⁻¹ * (-2 * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 3)).re)) t := by
  have hraw :=
    (hasDerivAt_second_deriv_negLogDet_add_smul A H hunit).const_mul (Fintype.card n : ℝ)⁻¹
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_add_smul A H hunit] with s hs
  rw [second_deriv_intensiveNegLogDet_add_smul A H hs,
    second_deriv_negLogDet_add_smul A H hs]

/-- Third directional derivative of `intensiveNegLogDet` along `A + s • H`. -/
theorem third_deriv_intensiveNegLogDet_add_smul (A H : Mat) {t : ℝ}
    (hunit : IsUnit (A + t • H)) :
    deriv (deriv (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H)))) t =
      -2 * ((Fintype.card n : ℝ)⁻¹ * (Matrix.trace (((A + t • H)⁻¹ * H) ^ 3)).re) := by
  rw [(hasDerivAt_second_deriv_intensiveNegLogDet_add_smul A H hunit).deriv]
  ring

/-- Third directional derivative of `intensiveNegLogDet` at `t = 0` equals
`-2 * intensiveTraceCubic n A H`. -/
theorem third_deriv_intensiveNegLogDet_add_smul_zero (A H : Mat) (hA : IsUnit A) :
    deriv (deriv (deriv (fun s : ℝ => intensiveNegLogDet n (A + s • H)))) 0 =
      -2 * intensiveTraceCubic n A H := by
  simpa [intensiveTraceCubic, traceCubic, reTrace] using
    third_deriv_intensiveNegLogDet_add_smul A H (t := 0) (by simpa using hA)

/-! ===========================================================================
    Section 2: The Rank-One Projection Counterexample to Uniform Positivity &
    Self-Concordance Blow-Up (`D²F_d(I)[-2P, -2P] = 4 / d`, `I - 2P ≰ 0`)
    =========================================================================== -/

/-- For any idempotent matrix `P * P = P` with `reTrace P = 1`, its quadratic and cubic
trace forms at the identity `1` both equal `1`, and `traceQuadratic 1 ((-2 : ℝ) • P) = 4`. -/
theorem traceQuadratic_and_cubic_of_idempotent_trace_one
    {P : Mat} (hP : P * P = P) (htr : reTrace P = 1) :
    traceQuadratic (1 : Mat) P = 1 ∧
    traceCubic (1 : Mat) P = 1 ∧
    traceQuadratic (1 : Mat) ((-2 : ℝ) • P) = 4 := by
  have hP2 : P ^ 2 = P := by rw [sq, hP]
  have hP3 : P ^ 3 = P := by rw [pow_succ, hP2, hP]
  have hQ : traceQuadratic (1 : Mat) P = 1 := by
    unfold traceQuadratic
    rw [inv_one, one_mul, hP2, htr]
  have hC : traceCubic (1 : Mat) P = 1 := by
    unfold traceCubic
    rw [inv_one, one_mul, hP3, htr]
  have hQ2 : traceQuadratic (1 : Mat) ((-2 : ℝ) • P) = 4 := by
    unfold traceQuadratic reTrace
    rw [inv_one, one_mul, smul_pow, hP2, Matrix.trace_smul]
    change (((-2 : ℝ) ^ 2) • Matrix.trace P).re = 4
    rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    change (-2 : ℝ) ^ 2 * reTrace P = 4
    rw [htr]
    ring
  exact ⟨hQ, hC, hQ2⟩

/-- **Intensive Trace Energy of `-2P` & Self-Concordance Ratio Blow-Up**:
For any rank-one idempotent `P * P = P` (`reTrace P = 1`) on `n × n` matrices:
1. `intensiveTraceQuadratic n 1 ((-2 : ℝ) • P) = 4 / Fintype.card n`,
2. `deriv (deriv (fun s => intensiveNegLogDet n (1 + s • ((-2 : ℝ) • P)))) 0 = 4 / Fintype.card n`,
3. `(-2 * intensiveTraceCubic n 1 P) ^ 2 = 4 * (Fintype.card n : ℝ) * (intensiveTraceQuadratic n 1 P) ^ 3`. -/
theorem intensive_idempotent_hessian_and_self_concordance_blowup
    [Nonempty n] {P : Mat} (hP : P * P = P) (htr : reTrace P = 1) :
    intensiveTraceQuadratic n (1 : Mat) ((-2 : ℝ) • P) = 4 / (Fintype.card n : ℝ) ∧
    deriv (deriv (fun s : ℝ => intensiveNegLogDet n ((1 : Mat) + s • ((-2 : ℝ) • P)))) 0 =
      4 / (Fintype.card n : ℝ) ∧
    (-2 * intensiveTraceCubic n (1 : Mat) P) ^ 2 =
      4 * (Fintype.card n : ℝ) * (intensiveTraceQuadratic n (1 : Mat) P) ^ 3 := by
  have h1 := traceQuadratic_and_cubic_of_idempotent_trace_one hP htr
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by positivity
  have hIntQ2 : intensiveTraceQuadratic n (1 : Mat) ((-2 : ℝ) • P) = 4 / (Fintype.card n : ℝ) := by
    unfold intensiveTraceQuadratic
    rw [h1.2.2, div_eq_inv_mul]
  refine ⟨hIntQ2, ?_, ?_⟩
  · rw [second_deriv_intensiveNegLogDet_add_smul_zero (1 : Mat) ((-2 : ℝ) • P) isUnit_one, hIntQ2]
  · unfold intensiveTraceCubic intensiveTraceQuadratic
    rw [h1.1, h1.2.1]
    field_simp [hcard]
    ring

/-- Concrete rank-one projection `E₀₀ = Matrix.single 0 0 1` on `Fin (d + 1)`. -/
def rankOneProj (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.single 0 0 1

theorem rankOneProj_mul_self (d : ℕ) :
    rankOneProj d * rankOneProj d = rankOneProj d := by
  unfold rankOneProj
  simp

theorem rankOneProj_reTrace (d : ℕ) :
    reTrace (rankOneProj d) = 1 := by
  unfold reTrace rankOneProj Matrix.trace
  simp

/-- **The Normalized Trace Counterexample to Uniform Positivity**:
In every dimension `d + 1`:
1. The intensive Hessian at `I` in the direction `H = -2 E₀₀` is `4 / (d + 1)`, which tends to `0`
   as `d → ∞`,
2. Yet `I + H = 1 + (-2 : ℝ) • E₀₀` has `(0, 0)`-entry equal to `-1`, so its quadratic form on
   `e₀ = Pi.single 0 1` is `-1 < 0`, and `1 + (-2 : ℝ) • E₀₀` is **not** positive semidefinite
   (`¬ PosSemidef (1 + (-2 : ℝ) • rankOneProj d)`). -/
theorem intensive_trace_counterexample_to_uniform_positivity (d : ℕ) :
    intensiveTraceQuadratic (Fin (d + 1))
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ((-2 : ℝ) • rankOneProj d) =
      4 / ((d + 1 : ℕ) : ℝ) ∧
    (((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) + (-2 : ℝ) • rankOneProj d) 0 0).re = -1 ∧
    ¬ ((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) + (-2 : ℝ) • rankOneProj d).PosSemidef := by
  have hInt :=
    (intensive_idempotent_hessian_and_self_concordance_blowup
      (rankOneProj_mul_self d) (rankOneProj_reTrace d)).1
  rw [Fintype.card_fin] at hInt
  have hEntry :
      (((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) + (-2 : ℝ) • rankOneProj d) 0 0).re = -1 := by
    simp [rankOneProj]
    norm_num
  refine ⟨hInt, hEntry, ?_⟩
  intro hPos
  have hDiag :
      0 ≤ (((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) + (-2 : ℝ) • rankOneProj d) 0 0).re :=
    (Complex.nonneg_iff.mp (hPos.diag_nonneg (i := 0))).1
  rw [hEntry] at hDiag
  norm_num at hDiag

/-! ===========================================================================
    Section 3: Dimension-Independent Operator-Norm / Intensive-Trace Cubic Bound
    (`|D³F_d(P)[H,H,H]| ≤ 2 ‖P⁻¹/² H P⁻¹/²‖_op D²F_d(P)[H,H]`)
    =========================================================================== -/

/-- Every eigenvalue of a Hermitian matrix is bounded in absolute value by its `L²` operator norm. -/
theorem abs_eigenvalue_le_opNorm {B : Mat} (hB : B.IsHermitian) (i : n) :
    |hB.eigenvalues i| ≤ ‖B‖ := by
  conv_rhs => rw [hB.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  simpa only [Function.comp_apply, RCLike.norm_ofReal, Real.norm_eq_abs] using
    norm_le_pi_norm (RCLike.ofReal ∘ hB.eigenvalues : n → ℂ) i

/-- **Dimension-Independent Hermitian Cubic Trace Estimate**:
For any Hermitian matrix `B`, `|reTrace (B ^ 3)| ≤ ‖B‖ * reTrace (B ^ 2)`. -/
theorem abs_reTrace_cube_le_opNorm_mul_reTrace_sq {B : Mat} (hB : B.IsHermitian) :
    |reTrace (B ^ 3)| ≤ ‖B‖ * reTrace (B ^ 2) := by
  rw [reTrace_pow_eq_sum_eigenvalues hB 3, reTrace_pow_eq_sum_eigenvalues hB 2, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs (fun i => hB.eigenvalues i ^ 3) Finset.univ).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hpow : |hB.eigenvalues i ^ 3| = |hB.eigenvalues i| * hB.eigenvalues i ^ 2 := by
    rw [abs_pow, pow_succ', sq_abs]
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (abs_eigenvalue_le_opNorm hB i) (sq_nonneg _)

/-- **Dimension-Independent Unnormalized Cubic Trace Bound**:
For any strictly positive base point `P` and self-adjoint variation `H`,
`|traceCubic P H| ≤ ‖normalizedVariation P H‖ * traceQuadratic P H`. -/
theorem abs_traceCubic_le_opNorm_normalizedVariation_mul_traceQuadratic
    {P H : Mat} (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    |traceCubic P H| ≤ ‖normalizedVariation P H‖ * traceQuadratic P H := by
  rw [traceCubic_eq_normalized hP, traceQuadratic_eq_normalized hP]
  exact abs_reTrace_cube_le_opNorm_mul_reTrace_sq (normalizedVariation_isHermitian P hH)

/-- **Dimension-Independent Intensive Cubic Bound**:
For any strictly positive base point `P` and self-adjoint variation `H`, the intensive third
directional derivative is controlled by `2 ‖P⁻¹/² H P⁻¹/²‖_op` times the intensive second
directional derivative, with **no dimension factor**:
`|D³F_d(P)[H,H,H]| ≤ 2 * ‖normalizedVariation P H‖ * D²F_d(P)[H,H]`. -/
theorem abs_third_deriv_intensiveNegLogDet_le_two_opNorm_mul_second_deriv
    {P H : Mat} (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    |deriv (deriv (deriv (fun s : ℝ => intensiveNegLogDet n (P + s • H)))) 0| ≤
      2 * ‖normalizedVariation P H‖ *
        deriv (deriv (fun s : ℝ => intensiveNegLogDet n (P + s • H))) 0 := by
  rw [third_deriv_intensiveNegLogDet_add_smul_zero P H hP.isUnit,
    second_deriv_intensiveNegLogDet_add_smul_zero P H hP.isUnit]
  unfold intensiveTraceCubic intensiveTraceQuadratic
  have hcard_nonneg : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_mul, abs_of_nonneg hcard_nonneg]
  have hcub := abs_traceCubic_le_opNorm_normalizedVariation_mul_traceQuadratic hP hH
  calc
    2 * ((Fintype.card n : ℝ)⁻¹ * |traceCubic P H|)
      = (2 * (Fintype.card n : ℝ)⁻¹) * |traceCubic P H| := by ring
    _ ≤ (2 * (Fintype.card n : ℝ)⁻¹) * (‖normalizedVariation P H‖ * traceQuadratic P H) :=
      mul_le_mul_of_nonneg_left hcub (by positivity)
    _ = 2 * ‖normalizedVariation P H‖ * ((Fintype.card n : ℝ)⁻¹ * traceQuadratic P H) := by ring

/-! ===========================================================================
    Section 4: Direction 1 — Peirce–Hodge Centralizer vs. Annihilator Separation
    & Algebraic Homotopy Identity
    =========================================================================== -/

/-- **Centralizer vs. Peirce–Hodge Kernel Separation**:
For any nonzero matrix `N : Matrix n n ℂ`, the identity matrix `1` commutes with `N`
(`N * 1 - 1 * N = 0`), yet `1` is **not** in the Peirce–Hodge kernel
`jordanLeft (N * Nᴴ + Nᴴ * N) 1 ≠ 0`. -/
theorem centralizer_ne_peirce_hodge_kernel
    {N : Mat} (hN : N ≠ 0) :
    N * (1 : Mat) - (1 : Mat) * N = 0 ∧
    jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) (1 : Mat) ≠ 0 := by
  refine ⟨by noncomm_ring, ?_⟩
  intro hZero
  have hAnn := (hs_jordan_gram_apply_eq_zero_iff N (1 : Mat)).mp hZero
  have hN1 : N * (1 : Mat) = N := Matrix.mul_one N
  rw [hN1] at hAnn
  exact hN hAnn.1

/-- **Intrinsic Graded Differential + Metric-Style Dual Anticommutator**:
In any `R`-algebra `A` with involutive automorphism `θ` (`θ (θ X) = X`) and odd operators
`Q, Q_dag : A` (`θ Q = -Q`, `θ Q_dag = -Q_dag`), let `d_Q(X) = Q * X - θ X * Q` and
`d_dag(X) = Q_dag * X + θ X * Q_dag`. Then for every `X : A`:
`d_Q (d_dag X) + d_dag (d_Q X) = (Q * Q_dag + Q_dag * Q) * X + X * (Q * Q_dag + Q_dag * Q)`. -/
theorem intrinsic_graded_hodge_anticommutator_apply
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (θ : A ≃ₐ[R] A) (hθ : Function.Involutive θ)
    (Q Q_dag : A) (hQ : θ Q = -Q) (hQ_dag : θ Q_dag = -Q_dag) (X : A) :
    let d_dag : A → A := fun Y => Q_dag * Y + θ Y * Q_dag
    gradedAdjoint θ Q (d_dag X) + d_dag (gradedAdjoint θ Q X) =
      (Q * Q_dag + Q_dag * Q) * X + X * (Q * Q_dag + Q_dag * Q) := by
  intro d_dag
  dsimp [d_dag, gradedAdjoint]
  simp only [map_add, map_sub, map_mul, hQ, hQ_dag, hθ X]
  noncomm_ring

/-! ===========================================================================
    Section 5: Direction 2 — Factorial-Weighted Fock Adjoint & Coherent Shifted
    Oscillator Ground State Resolving the Nuclear Resolvent Obstruction
    =========================================================================== -/

/-- Scalar phonon creation shift `(a† c)_0 = 0`, `(a† c)_{n+1} = c_n`. -/
def scalarPhononCreate (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => c m

/-- Scalar phonon annihilation weighted shift `(a d)_m = (m + 1) d_{m + 1}`. -/
def scalarPhononAnnihilate (d : ℕ → ℝ) (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) * d (m + 1)

/-- Finite-horizon factorial-weighted Fock inner product
`⟨c, d⟩_{Fock, N} = ∑_{m < N + 1} m! * c_m * d_m`. -/
def fockWeightedPairing (N : ℕ) (c d : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) * c m * d m

/-- **Factorial-Weighted Fock Adjoint Theorem**:
For any horizon `N : ℕ` and sequences `c, d : ℕ → ℝ` with `c N = 0`, the creation shift
`scalarPhononCreate` and weighted annihilation shift `scalarPhononAnnihilate` are exact
adjoints with respect to `fockWeightedPairing N`:
`fockWeightedPairing N (scalarPhononCreate c) d = fockWeightedPairing N c (scalarPhononAnnihilate d)`. -/
theorem fockWeightedPairing_create_eq_annihilate
    (N : ℕ) (c d : ℕ → ℝ) (hcN : c N = 0) :
    fockWeightedPairing N (scalarPhononCreate c) d =
      fockWeightedPairing N c (scalarPhononAnnihilate d) := by
  unfold fockWeightedPairing
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [scalarPhononCreate, scalarPhononAnnihilate, mul_zero, zero_mul, add_zero, hcN]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- Coherent ground-state sequence `c_coh(m) = (-g / ω)^m / m!` at the shifted oscillator
ground-state energy `E₀ = -g² / ω`. -/
def coherentGroundCoeff (omega g : ℝ) (m : ℕ) : ℝ :=
  (-g / omega) ^ m / (Nat.factorial m : ℝ)

/-- **Shifted Oscillator Coherent Ground State Theorem**:
At the shifted oscillator energy `E₀ = -g² / ω` (`ω ≠ 0`), the coherent sequence
`coherentGroundCoeff omega g`:
1. Satisfies the initial and step balance equations of the nuclear phonon Hamiltonian,
2. Has factorial-weighted Fock norm summand `(m! : ℝ) * coherentGroundCoeff omega g m ^ 2 = ((g / ω) ^ 2) ^ m / m!`,
3. Is `Summable` in the factorial-weighted Fock norm (`Summable (fun m => (m! : ℝ) * coherentGroundCoeff omega g m ^ 2)`). -/
theorem coherentGroundCoeff_balance_and_fock_summable
    (omega g : ℝ) (h_omega : omega ≠ 0) (m : ℕ) :
    let E₀ := -g ^ 2 / omega
    let c := coherentGroundCoeff omega g
    (g * c 1 = E₀ * c 0) ∧
    (omega * ((m + 1 : ℕ) : ℝ) * c (m + 1) +
        g * (c m + ((m + 2 : ℕ) : ℝ) * c (m + 2)) =
      E₀ * c (m + 1)) ∧
    ((Nat.factorial m : ℝ) * (c m) ^ 2 = ((g / omega) ^ 2) ^ m / (Nat.factorial m : ℝ)) ∧
    Summable (fun k : ℕ => (Nat.factorial k : ℝ) * (c k) ^ 2) := by
  intro E₀ c
  have hfac_m : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  have hfac_m1 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := by positivity
  have hfac_m2 : (Nat.factorial (m + 2) : ℝ) ≠ 0 := by positivity
  have h0 : g * c 1 = E₀ * c 0 := by
    dsimp [c, coherentGroundCoeff, E₀]
    norm_num
    field_simp [h_omega]
  have hstep :
      omega * ((m + 1 : ℕ) : ℝ) * c (m + 1) +
          g * (c m + ((m + 2 : ℕ) : ℝ) * c (m + 2)) =
        E₀ * c (m + 1) := by
    set q : ℝ := (-g / omega) ^ m
    have hp1 : (-g / omega) ^ (m + 1) = q * (-g / omega) := pow_succ _ m
    have hp2 : (-g / omega) ^ (m + 2) = q * (-g / omega) * (-g / omega) := by
      rw [pow_succ _ (m + 1), hp1]
    dsimp [c, coherentGroundCoeff, E₀]
    rw [hp2, hp1]
    change omega * ((m + 1 : ℕ) : ℝ) * (q * (-g / omega) / (Nat.factorial (m + 1) : ℝ)) +
        g * (q / (Nat.factorial m : ℝ) +
          ((m + 2 : ℕ) : ℝ) * (q * (-g / omega) * (-g / omega) / (Nat.factorial (m + 2) : ℝ))) =
      -g ^ 2 / omega * (q * (-g / omega) / (Nat.factorial (m + 1) : ℝ))
    rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm2 : ((m + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [h_omega, hfac_m, hm1, hm2]
    ring
  have hnorm_term : ∀ k : ℕ,
      (Nat.factorial k : ℝ) * (c k) ^ 2 = ((g / omega) ^ 2) ^ k / (Nat.factorial k : ℝ) := by
    intro k
    dsimp [c, coherentGroundCoeff]
    have hfk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    rw [div_pow, ← pow_mul, mul_comm k 2, pow_mul]
    have hneg_sq : (-g / omega) ^ 2 = (g / omega) ^ 2 := by ring
    rw [hneg_sq]
    field_simp [hfk]
  refine ⟨h0, hstep, hnorm_term m, ?_⟩
  simp_rw [hnorm_term]
  exact Real.summable_pow_div_factorial ((g / omega) ^ 2)

/-! ===========================================================================
    Section 6: Concrete Non-Commutative Complex Matrix Witness (`T16`)
    =========================================================================== -/

/-- Concrete `2 × 2` complex diagonal projection `E₀₀`. -/
def witnessComplexProj2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Concrete `2 × 2` complex off-diagonal nilpotent `E₀₁`. -/
def witnessComplexNilp2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- **Trap T16 Non-Commutativity Witness (`witnessComplexProj2_witnessComplexNilp2_noncomm`)**:
In `Matrix (Fin 2) (Fin 2) ℂ`, `witnessComplexProj2` and `witnessComplexNilp2` do not commute. -/
theorem witnessComplexProj2_witnessComplexNilp2_noncomm :
    (witnessComplexProj2 : Matrix (Fin 2) (Fin 2) ℂ) *
        (witnessComplexNilp2 : Matrix (Fin 2) (Fin 2) ℂ) ≠
      (witnessComplexNilp2 : Matrix (Fin 2) (Fin 2) ℂ) *
        (witnessComplexProj2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [witnessComplexProj2, witnessComplexNilp2, Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Canonical.IntensiveLogDetPositivityTension
