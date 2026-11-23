/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import InfoGeometry.Core.PeirceDecomposition

/-!
# InfoGeometry.Krein.KreinJordanSpectralObstructions

Three exact, finite-dimensional `2 × 2` operator counterexamples certifying why
naive Banach/Hilbert trace-class arguments break on indefinite Krein signatures,
oblique biorthogonal (Markushevich) bases, and parabolic eigenvalue coalescence:

1. **Indefinite Krein Trace vs. Positive Norm (`diag(1, -1)` — `ERRATA F8`):**
   `kreinPolarityMat = diag(1, -1)` has vanishing algebraic trace `Tr(Γ) = 0`,
   yet positive Hilbert–Schmidt squared norm `Tr(Γ²) = 2 > 0` and nuclear
   eigenvalue-sum `|1| + |-1| = 2 > 0`.
2. **Oblique Markushevich Dual / Projector Blow-Up (`Ω_θ` — p. 444):**
   For unit vectors `e₁ = (1, 0)` and `e₂(θ) = (cos θ, sin θ)` (`‖e₁‖ = ‖e₂(θ)‖ = 1`),
   the oblique idempotent `Ω_θ = [[1, -cot θ], [0, 0]]` satisfies `Ω_θ² = Ω_θ`,
   `Ω_θ e₁ = e₁`, and `Ω_θ e₂(θ) = 0`, yet its Frobenius squared norm
   `‖Ω_θ‖_F² = 1 + cot² θ = (sin θ)⁻²` is unbounded above as `θ → 0⁺`.
3. **Parabolic Jordan Coalescence Blow-Up (`P_{ρ₁}` — p. 451):**
   For `A(ρ₁, ρ₂) = [[ρ₁, 1], [0, ρ₂]]` (`ρ₁ ≠ ρ₂`), the rank-1 spectral
   idempotent `P_{ρ₁} = [[1, (ρ₁ - ρ₂)⁻¹], [0, 0]]` satisfies `P_{ρ₁}² = P_{ρ₁}`
   and `A P_{ρ₁} = ρ₁ P_{ρ₁}` with off-diagonal entry blowing up as
   `|ρ₁ - ρ₂|⁻¹ → ∞` as `ρ₂ → ρ₁`, while at `ρ₁ = ρ₂` the operator collapses
   to a non-diagonalizable Jordan block with nilpotent part `N = [[0, 1], [0, 0]]`
   (`N² = 0`, `N ≠ 0`).
-/

noncomputable section

namespace InfoGeometry.Krein.KreinJordanSpectralObstructions

open scoped Matrix

/-! ## 1. Witness 1 (`ERRATA F8`): Indefinite Krein polarity `Γ = diag(1, -1)` -/

/-- Indefinite Krein polarity involution `Γ = diag(1, -1)` on `ℝ²`. -/
def kreinPolarityMat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, -1]]

/-- Companion flip matrix `X = [[0, 1], [1, 0]]` on `ℝ²` (non-commutativity partner). -/
def kreinSwapMat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![1, 0]]

theorem kreinPolarityMat_mul_kreinSwapMat_ne :
    kreinPolarityMat * kreinSwapMat ≠ kreinSwapMat * kreinPolarityMat := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [kreinPolarityMat, kreinSwapMat, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **Witness 1 (`ERRATA F8`)**: `Γ = diag(1, -1)` has `Γ² = 1` and vanishing
algebraic trace `Tr(Γ) = 0`, yet strictly positive Hilbert–Schmidt squared norm
`Tr(Γ²) = 2` and absolute diagonal sum `2`. -/
theorem kreinPolarity_trace_zero_yet_norm_two :
    (kreinPolarityMat * kreinPolarityMat = 1) ∧
    (Matrix.trace kreinPolarityMat = 0) ∧
    (Matrix.trace (kreinPolarityMat * kreinPolarityMat) = 2) ∧
    (|kreinPolarityMat 0 0| + |kreinPolarityMat 1 1| = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinPolarityMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · norm_num [kreinPolarityMat, Matrix.trace, Fin.sum_univ_two]
  · norm_num [kreinPolarityMat, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [kreinPolarityMat]

/-- Orthogonal Walsh/Hadamard rotation `H = (1/√2) * [[1, 1], [1, -1]]` on `ℝ²`
rotating the diagonal Peirce frame into the null lightcone of `Γ = diag(1, -1)`. -/
def walshMat : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 2)⁻¹ • Matrix.of ![![1, 1], ![1, -1]]

theorem walshMat_mul_self :
    walshMat * walshMat = 1 := by
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walshMat, Matrix.mul_apply, Fin.sum_univ_two, hsq]
  all_goals norm_num

/-- Walsh rotation conjugates `Γ = diag(1, -1)` to the off-diagonal swap
`X = [[0, 1], [1, 0]]`, wiping out its diagonal entries completely. -/
theorem walsh_conjugated_kreinPolarity :
    walshMat * kreinPolarityMat * walshMat = kreinSwapMat := by
  have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walshMat, kreinPolarityMat, kreinSwapMat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-- **Complete `ERRATA F8` Refutation (`2 → 0` under Walsh rotation)**:
The diagonal-expectation sum `∑_i |⟨T e_i, e_i⟩|` is `2` in the standard basis
and `0` in the orthonormal Walsh basis, refuting basis-invariance for indefinite
trace-class operators. -/
theorem errata_F8_walsh_basis_dependence :
    (|kreinPolarityMat 0 0| + |kreinPolarityMat 1 1| = 2) ∧
    (|(walshMat * kreinPolarityMat * walshMat) 0 0| +
     |(walshMat * kreinPolarityMat * walshMat) 1 1| = 0) := by
  rw [walsh_conjugated_kreinPolarity]
  constructor <;> norm_num [kreinPolarityMat, kreinSwapMat]

/-! ## 1b. Witness 1b (`ERRATA F9`): Peirce cut `P₀ = diag(1, 0)` + parabolic nilpotent `X = e₂₁` -/

/-- Conscious Peirce cut `P₀ = diag(1, 0)` on `ℝ²`. -/
def peirceCutP0 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, 0]]

/-- Outward parabolic Jordan nilpotent `X = e₂₁ = [[0, 0], [1, 0]]` on `ℝ²`. -/
def outwardNilpotentX : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 0], ![1, 0]]

/-- **Complete `ERRATA F9` Refutation (`P₀ X = 0` vs `X P₀ = X`)**:
Although the algebraic trace is cyclic (`Tr(P₀ X) = Tr(X P₀) = 0`), the
products have strictly different norms (`‖P₀ X‖_F² = 0` vs `‖X P₀‖_F² = 1`),
refuting trace-norm symmetry `‖AT‖_Tr = ‖TA‖_Tr`. -/
theorem errata_F9_trace_norm_asymmetry :
    (peirceCutP0 * peirceCutP0 = peirceCutP0) ∧
    (outwardNilpotentX * outwardNilpotentX = 0) ∧
    (Matrix.trace (peirceCutP0 * outwardNilpotentX) = 0) ∧
    (Matrix.trace (outwardNilpotentX * peirceCutP0) = 0) ∧
    (peirceCutP0 * outwardNilpotentX = 0) ∧
    (outwardNilpotentX * peirceCutP0 = outwardNilpotentX) ∧
    (peirceCutP0 * outwardNilpotentX ≠ outwardNilpotentX * peirceCutP0) := by
  have hPX : peirceCutP0 * outwardNilpotentX = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCutP0, outwardNilpotentX, Matrix.mul_apply, Fin.sum_univ_two]
  have hXP : outwardNilpotentX * peirceCutP0 = outwardNilpotentX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCutP0, outwardNilpotentX, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, hPX, hXP, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCutP0, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [outwardNilpotentX, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hPX]; simp
  · rw [hXP]; norm_num [outwardNilpotentX, Matrix.trace, Fin.sum_univ_two]
  · rw [hPX, hXP]
    intro h0
    have h10 := congrFun (congrFun h0 1) 0
    norm_num [outwardNilpotentX] at h10

/-! ## 2. Witness 2 (p. 444): Oblique Markushevich dual / idempotent blow-up `Ω_θ` -/

/-- First standard unit basis vector `e₁ = (1, 0)`. -/
def unitVec1 : Fin 2 → ℝ := ![1, 0]

/-- Second unit basis vector `e₂(θ) = (cos θ, sin θ)` at tilt angle `θ`. -/
def unitVecTilt (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- Both basis vectors have exact Euclidean norm squared `1` (uniformly bounded
away from zero for all `θ : ℝ`). -/
theorem unitVec_norms_eq_one (θ : ℝ) :
    (unitVec1 0) ^ 2 + (unitVec1 1) ^ 2 = 1 ∧
    (unitVecTilt θ 0) ^ 2 + (unitVecTilt θ 1) ^ 2 = 1 := by
  constructor
  · norm_num [unitVec1]
  · simp [unitVecTilt, Real.cos_sq_add_sin_sq]

/-- Oblique idempotent `Ω_θ = [[1, -cos θ / sin θ], [0, 0]]` projecting onto
`span{e₁}` along `span{e₂(θ)}`. -/
def obliqueProj (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, -(Real.cos θ / Real.sin θ)], ![0, 0]]

/-- Frobenius squared norm `∑_{i,j} M_{ij}²` of a `2 × 2` real matrix. -/
def frobNormSq (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0) ^ 2 + (M 0 1) ^ 2 + (M 1 0) ^ 2 + (M 1 1) ^ 2

theorem obliqueProj_idempotent (θ : ℝ) :
    obliqueProj θ * obliqueProj θ = obliqueProj θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [obliqueProj, Matrix.mul_apply, Fin.sum_univ_two]

theorem obliqueProj_biorthogonal (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    Matrix.mulVec (obliqueProj θ) unitVec1 = unitVec1 ∧
    Matrix.mulVec (obliqueProj θ) (unitVecTilt θ) = 0 := by
  constructor
  · funext i
    fin_cases i <;> simp [obliqueProj, unitVec1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · funext i
    fin_cases i
    · simp [obliqueProj, unitVecTilt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hsin]
      ring
    · simp [obliqueProj, unitVecTilt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Exact Frobenius norm formula: `‖Ω_θ‖_F² = (sin θ)⁻²`. -/
theorem frobNormSq_obliqueProj (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    frobNormSq (obliqueProj θ) = (Real.sin θ)⁻¹ ^ 2 := by
  simp only [frobNormSq, obliqueProj, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcs := Real.cos_sq_add_sin_sq θ
  field_simp [hsin]
  calc
    Real.sin θ ^ 2 + Real.cos θ ^ 2 + Real.sin θ ^ 2 * 0 ^ 2 + Real.sin θ ^ 2 * 0 ^ 2
        = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by simp [add_comm]
    _ = 1 := hcs

/-- **Witness 2 (p. 444 — Unbounded Biorthogonal Duals)**:
For every bound `M : ℝ`, there exists an angle `θ` with `sin θ ≠ 0` such that
the unit basis `(e₁, e₂(θ))` has oblique biorthogonal projector norm
`‖Ω_θ‖_F² > M`. -/
theorem obliqueProj_frobNormSq_unbounded (M : ℝ) :
    ∃ θ : ℝ, Real.sin θ ≠ 0 ∧ M < frobNormSq (obliqueProj θ) := by
  let ε : ℝ := (max 1 (|M| + 1))⁻¹
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_le_one : ε ≤ 1 := by
    dsimp [ε]
    exact inv_le_one_of_one_le₀ (le_max_left 1 (|M| + 1))
  have hsin_pos : 0 < Real.sin ε := by
    apply Real.sin_pos_of_pos_of_lt_pi hε_pos
    linarith [Real.pi_gt_three]
  have hsin_le : Real.sin ε ≤ ε := le_of_lt (Real.sin_lt hε_pos)
  refine ⟨ε, ne_of_gt hsin_pos, ?_⟩
  rw [frobNormSq_obliqueProj ε (ne_of_gt hsin_pos)]
  have hinv_ge : ε⁻¹ ≤ (Real.sin ε)⁻¹ := by
    exact inv_anti₀ hsin_pos hsin_le
  have h1 : 1 ≤ ε⁻¹ := by
    dsimp [ε]
    rw [inv_inv]
    exact le_max_left 1 (|M| + 1)
  have hM : M < ε⁻¹ := by
    dsimp [ε]
    rw [inv_inv]
    calc
      M ≤ |M| := le_abs_self M
      _ < |M| + 1 := lt_add_one _
      _ ≤ max 1 (|M| + 1) := le_max_right 1 (|M| + 1)
  have hsq : ε⁻¹ ≤ (Real.sin ε)⁻¹ ^ 2 := by
    calc
      ε⁻¹ = ε⁻¹ * 1 := (mul_one _).symm
      _ ≤ (Real.sin ε)⁻¹ * (Real.sin ε)⁻¹ :=
        mul_le_mul hinv_ge (le_trans h1 hinv_ge) zero_le_one (le_trans (le_trans zero_le_one h1) hinv_ge)
      _ = (Real.sin ε)⁻¹ ^ 2 := (sq _).symm
  exact lt_of_lt_of_le hM hsq

/-! ## 3. Witness 3 (p. 451): Parabolic Jordan coalescence & nilpotent limit -/

/-- `2 × 2` Jordan-approaching upper-triangular matrix `A(ρ₁, ρ₂) = [[ρ₁, 1], [0, ρ₂]]`. -/
def jordanApproachMat (ρ₁ ρ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![ρ₁, 1], ![0, ρ₂]]

/-- The eigenvector matrix for the distinct eigenvalues of `jordanApproachMat`. -/
def jordanApproachEigenbasis (ρ₁ ρ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 1], ![0, ρ₂ - ρ₁]]

/-- The inverse eigenvector matrix when the two eigenvalues are distinct. -/
def jordanApproachEigenbasisInv (ρ₁ ρ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, -(ρ₂ - ρ₁)⁻¹], ![0, (ρ₂ - ρ₁)⁻¹]]

/-- The diagonal operator in the ordered eigenbasis. -/
def jordanApproachDiagonal (ρ₁ ρ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then ρ₁ else ρ₂)

/-- The displayed eigenvector matrix and its inverse multiply to the identity off
the repeated-eigenvalue locus. -/
theorem jordanApproachEigenbasis_inverse_identities (ρ₁ ρ₂ : ℝ)
    (hne : ρ₁ ≠ ρ₂) :
    jordanApproachEigenbasisInv ρ₁ ρ₂ * jordanApproachEigenbasis ρ₁ ρ₂ = 1 ∧
      jordanApproachEigenbasis ρ₁ ρ₂ * jordanApproachEigenbasisInv ρ₁ ρ₂ = 1 := by
  have hsub : ρ₂ - ρ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [jordanApproachEigenbasisInv, jordanApproachEigenbasis,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp [hsub]
    all_goals ring
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [jordanApproachEigenbasis, jordanApproachEigenbasisInv,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp [hsub]

/-- In the eigenvector basis, `jordanApproachMat` acts by the two eigenvalues. -/
theorem jordanApproachMat_mul_eigenbasis (ρ₁ ρ₂ : ℝ) :
    jordanApproachMat ρ₁ ρ₂ * jordanApproachEigenbasis ρ₁ ρ₂ =
      jordanApproachEigenbasis ρ₁ ρ₂ * jordanApproachDiagonal ρ₁ ρ₂ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [jordanApproachMat, jordanApproachEigenbasis, jordanApproachDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  all_goals ring

/-- For distinct diagonal entries, the upper triangular family is similar to a
diagonal matrix. Its coalescence at equal entries is the defective Jordan case
recorded by `parabolic_jordan_coalescence_witness`. -/
theorem jordanApproachMat_diagonalizable_of_ne (ρ₁ ρ₂ : ℝ)
    (hne : ρ₁ ≠ ρ₂) :
    jordanApproachEigenbasisInv ρ₁ ρ₂ * jordanApproachMat ρ₁ ρ₂ *
      jordanApproachEigenbasis ρ₁ ρ₂ = jordanApproachDiagonal ρ₁ ρ₂ := by
  have hInv := jordanApproachEigenbasis_inverse_identities ρ₁ ρ₂ hne
  calc
    _ = jordanApproachEigenbasisInv ρ₁ ρ₂ *
        (jordanApproachMat ρ₁ ρ₂ * jordanApproachEigenbasis ρ₁ ρ₂) := by
          simp [Matrix.mul_assoc]
    _ = jordanApproachEigenbasisInv ρ₁ ρ₂ *
        (jordanApproachEigenbasis ρ₁ ρ₂ * jordanApproachDiagonal ρ₁ ρ₂) := by
          rw [jordanApproachMat_mul_eigenbasis]
    _ = (jordanApproachEigenbasisInv ρ₁ ρ₂ * jordanApproachEigenbasis ρ₁ ρ₂) *
        jordanApproachDiagonal ρ₁ ρ₂ := by rw [← Matrix.mul_assoc]
    _ = jordanApproachDiagonal ρ₁ ρ₂ := by rw [hInv.1, Matrix.one_mul]

/-- Rank-1 spectral idempotent onto the `ρ₁`-eigenspace for `ρ₁ ≠ ρ₂`:
`P_{ρ₁} = [[1, (ρ₁ - ρ₂)⁻¹], [0, 0]]`. -/
def jordanSpectralProj (ρ₁ ρ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, (ρ₁ - ρ₂)⁻¹], ![0, 0]]

/-- Nilpotent `2 × 2` Jordan block `N = [[0, 1], [0, 0]]` at coalescence `ρ₁ = ρ₂`. -/
def jordanNilpotent : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![0, 0]]

/-- The distinct-eigenvalue spectral projector is the diagonal Peirce projection
plus its singular upper-right bridge component. -/
theorem jordanSpectralProj_eq_peirceCut_add_scaled_nilpotent (ρ₁ ρ₂ : ℝ) :
    jordanSpectralProj ρ₁ ρ₂ =
      peirceCutP0 + (ρ₁ - ρ₂)⁻¹ • jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanSpectralProj, peirceCutP0, jordanNilpotent, Matrix.add_apply,
      smul_eq_mul]

/-- The coalesced Jordan nilpotent is the upper-right Peirce corner of `peirceCutP0`. -/
theorem jordanNilpotent_eq_component10 :
    jordanNilpotent =
      InfoGeometry.Core.PeirceDecomposition.component10 peirceCutP0 jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanNilpotent, peirceCutP0,
      InfoGeometry.Core.PeirceDecomposition.component10,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The earlier lower-left nilpotent is the opposite Peirce corner. -/
theorem outwardNilpotentX_eq_component01 :
    outwardNilpotentX =
      InfoGeometry.Core.PeirceDecomposition.component01 peirceCutP0 outwardNilpotentX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [outwardNilpotentX, peirceCutP0,
      InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- These two nilpotents occupy opposite Peirce corners, square to zero by the
generic corner theorem, and their two products recover the complementary idempotents. -/
theorem jordan_and_outward_nilpotents_are_reciprocal_peirce_corners :
    jordanNilpotent ∈ InfoGeometry.Core.PeirceDecomposition.peirce10 peirceCutP0 ∧
    outwardNilpotentX ∈ InfoGeometry.Core.PeirceDecomposition.peirce01 peirceCutP0 ∧
    jordanNilpotent * jordanNilpotent = 0 ∧
    outwardNilpotentX * outwardNilpotentX = 0 ∧
    jordanNilpotent * outwardNilpotentX = peirceCutP0 ∧
    outwardNilpotentX * jordanNilpotent =
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent peirceCutP0 := by
  have hp : peirceCutP0 * peirceCutP0 = peirceCutP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCutP0, Matrix.mul_apply, Fin.sum_univ_two]
  have hq : InfoGeometry.Core.PeirceDecomposition.complementIdempotent peirceCutP0 =
      Matrix.of ![![0, 0], ![0, 1]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
        peirceCutP0, Matrix.one_apply]
  constructor
  · rw [jordanNilpotent_eq_component10]
    exact InfoGeometry.Core.PeirceDecomposition.component10_mem _ _
  constructor
  · rw [outwardNilpotentX_eq_component01]
    exact InfoGeometry.Core.PeirceDecomposition.component01_mem _ _
  constructor
  · rw [jordanNilpotent_eq_component10]
    exact InfoGeometry.Core.PeirceDecomposition.peirceCorner_sq_eq_zero
      (p := peirceCutP0)
      (q := InfoGeometry.Core.PeirceDecomposition.complementIdempotent peirceCutP0)
      (x := jordanNilpotent) (InfoGeometry.Core.PeirceDecomposition.complement_mul_idempotent
        peirceCutP0 hp)
  constructor
  · rw [outwardNilpotentX_eq_component01]
    exact InfoGeometry.Core.PeirceDecomposition.peirceCorner_sq_eq_zero
      (p := InfoGeometry.Core.PeirceDecomposition.complementIdempotent peirceCutP0)
      (q := peirceCutP0) (x := outwardNilpotentX)
      (InfoGeometry.Core.PeirceDecomposition.idempotent_mul_complement peirceCutP0 hp)
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jordanNilpotent, outwardNilpotentX, peirceCutP0,
        Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jordanNilpotent, outwardNilpotentX, peirceCutP0,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- **Witness 3 (p. 451 — Parabolic Jordan Coalescence)**:
1. For `ρ₁ ≠ ρ₂`, `P_{ρ₁}` is an idempotent spectral projector (`P² = P`,
   `A P = ρ₁ • P`) whose off-diagonal entry is `(ρ₁ - ρ₂)⁻¹` (blowing up as
   `ρ₂ → ρ₁`).
2. At coalescence `ρ₁ = ρ₂ = ρ`, `A(ρ, ρ) = ρ • 1 + N` where `N ≠ 0` and `N² = 0`. -/
theorem parabolic_jordan_coalescence_witness (ρ₁ ρ₂ : ℝ) (hne : ρ₁ ≠ ρ₂) :
    (jordanSpectralProj ρ₁ ρ₂ * jordanSpectralProj ρ₁ ρ₂ = jordanSpectralProj ρ₁ ρ₂) ∧
    (jordanApproachMat ρ₁ ρ₂ * jordanSpectralProj ρ₁ ρ₂ =
      ρ₁ • jordanSpectralProj ρ₁ ρ₂) ∧
    (jordanSpectralProj ρ₁ ρ₂ * jordanApproachMat ρ₁ ρ₂ =
      ρ₁ • jordanSpectralProj ρ₁ ρ₂) ∧
    (jordanApproachMat ρ₁ ρ₁ = ρ₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + jordanNilpotent) ∧
    (jordanNilpotent * jordanNilpotent = 0) ∧
    (jordanNilpotent ≠ 0) := by
  have hsub : ρ₁ - ρ₂ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanApproachMat, jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [jordanApproachMat, jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [jordanApproachMat, jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hsub]
      simp [sub_add_cancel]
    · simp [jordanApproachMat, jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [jordanApproachMat, jordanSpectralProj, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanApproachMat, jordanNilpotent]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h0
    have h01 := congrFun (congrFun h0 0) 1
    norm_num [jordanNilpotent] at h01

/-! ### 4. A stable invariant-cluster projection through internal coalescence -/

/-- A three-dimensional operator with a possibly coalescing two-dimensional
Jordan cluster and a separate scalar summand. -/
def jordanClusterMat (ρ₁ ρ₂ μ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![ρ₁, 1, 0], ![0, ρ₂, 0], ![0, 0, μ]]

/-- Projection onto the two-dimensional invariant cluster. This projection is
constant in the spectral parameters, so its entries remain bounded as the two
cluster eigenvalues coalesce. -/
def jordanClusterProj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]]

/-- The cluster projection is idempotent and commutes with the operator for all
parameters, including `ρ₁ = ρ₂`. Thus the invariant cluster survives the
parabolic collision even though its two individual rank-one spectral
projectors do not have a bounded limit. This is a finite block-diagonal
cluster result; it does not assert a Riesz projection theorem for general
operators. -/
theorem jordanClusterProj_idempotent_commutes (ρ₁ ρ₂ μ : ℝ) :
    jordanClusterProj * jordanClusterProj = jordanClusterProj ∧
    jordanClusterMat ρ₁ ρ₂ μ * jordanClusterProj =
      jordanClusterProj * jordanClusterMat ρ₁ ρ₂ μ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [jordanClusterProj, jordanClusterMat, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- Concrete 3×3 coordinate swap matrix witnessing non-commutativity with `jordanClusterProj`. -/
def jordanClusterFlipMat : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]]

/-- `jordanClusterProj` does not commute with `jordanClusterFlipMat` in `Matrix (Fin 3) (Fin 3) ℝ`. -/
theorem jordanClusterProj_mul_jordanClusterFlipMat_ne :
    jordanClusterProj * jordanClusterFlipMat ≠
      jordanClusterFlipMat * jordanClusterProj := by
  intro h
  have h12 := congrFun (congrFun h 1) 2
  norm_num [jordanClusterProj, jordanClusterFlipMat, Matrix.mul_apply,
    Fin.sum_univ_three] at h12

/-- At coalescence, a vector is an eigenvector for the repeated eigenvalue exactly
when its second coordinate vanishes. Thus the eigenspace is a single line. -/
theorem jordan_coalesced_eigenvector_iff_second_coordinate_zero (ρ : ℝ)
    (v : Fin 2 → ℝ) :
    jordanApproachMat ρ ρ *ᵥ v = ρ • v ↔ v 1 = 0 := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    simpa [Matrix.mulVec, dotProduct, jordanApproachMat, Fin.sum_univ_two] using h0
  · intro hv
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, jordanApproachMat, Fin.sum_univ_two, hv]
    · simp [Matrix.mulVec, dotProduct, jordanApproachMat, Fin.sum_univ_two]

end InfoGeometry.Krein.KreinJordanSpectralObstructions
