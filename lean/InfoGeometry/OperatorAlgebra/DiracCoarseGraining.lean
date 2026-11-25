/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralSkewIncidence
import InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
import InfoGeometry.OperatorAlgebra.RealMatrixSplit

/-!
# Skew incidence and positive Schur transport

Rectangular congruence transports the skew part of a real operator. The
symmetric part is supplied by the existing positive Schur-complement owner:
for positive definite `A,R`, its effective precision `C` satisfies
`C⁻¹ = R⁻¹ + Q A⁻¹ Qᵀ`. Thus the full response
`R⁻¹ + Q (A⁻¹ + P) Qᵀ` splits into `C⁻¹ + Q P Qᵀ`.

All multiplication orders are retained. Kernel transport is one-way; no
injectivity of the observation map is assumed. Operator addition is parallel
addition, not an assertion about elimination of arbitrary network vertices.
These are finite matrix and native incidence-graph statements, with no
continuum renormalization or physical CPT conclusion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DiracCoarseGraining

open Matrix
open PositiveCoarseGraining
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralSkewIncidence
open InfoGeometry.Twistor.RealTwistorIncidence
open InfoGeometry.Canonical.NeutralDualPairSplitting

variable {n m k : Type*}

/-- Parallel addition preserves real skew-symmetry. -/
theorem skew_add {P₁ P₂ : Matrix n n ℝ}
    (h₁ : P₁.transpose = -P₁) (h₂ : P₂.transpose = -P₂) :
    (P₁ + P₂).transpose = -(P₁ + P₂) := by
  simp only [Matrix.transpose_add, h₁, h₂, neg_add]

section Rectangular

variable [Fintype n] [Fintype m]

omit [Fintype m] in
/-- Congruence preserves skew-symmetry without an invertibility assumption. -/
theorem skew_congruence (Q : Matrix m n ℝ) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    (Q * P * Q.transpose).transpose = -(Q * P * Q.transpose) := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

omit [Fintype m] in
/-- Parallel sums are compatible with the observation map. -/
theorem congruence_add (Q : Matrix m n ℝ) (P₁ P₂ : Matrix n n ℝ) :
    Q * (P₁ + P₂) * Q.transpose =
      Q * P₁ * Q.transpose + Q * P₂ * Q.transpose := by
  simp only [Matrix.mul_add, Matrix.add_mul]

/-- Two successive observations give the congruence of their composite. -/
theorem congruence_comp
    (S : Matrix k m ℝ) (Q : Matrix m n ℝ) (P : Matrix n n ℝ) :
    (S * Q) * P * (S * Q).transpose =
      S * (Q * P * Q.transpose) * S.transpose := by
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- A coarse covector whose pullback is in the fine kernel stays in the kernel. -/
theorem congruence_kernel_transport (Q : Matrix m n ℝ) (P : Matrix n n ℝ)
    (ξ : m → ℝ) (hξ : P *ᵥ (Q.transpose *ᵥ ξ) = 0) :
    (Q * P * Q.transpose) *ᵥ ξ = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hξ, Matrix.mulVec_zero]

omit [Fintype m] in
/-- Rectangular congruence transports the native symmetric part. -/
theorem selfAdjointPart_congruence (Q : Matrix m n ℝ) (P : Matrix n n ℝ) :
    (selfAdjointPart ℝ (Q * P * Q.transpose) : Matrix m m ℝ) =
      Q * (selfAdjointPart ℝ P : Matrix n n ℝ) * Q.transpose := by
  simp only [RealMatrixSplit.selfAdjointPart_eq_half, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
    smul_add, Matrix.smul_mul, Matrix.mul_smul]

omit [Fintype m] in
/-- Rectangular congruence transports the native antisymmetric part. -/
theorem skewAdjointPart_congruence (Q : Matrix m n ℝ) (P : Matrix n n ℝ) :
    (skewAdjointPart ℝ (Q * P * Q.transpose) : Matrix m m ℝ) =
      Q * (skewAdjointPart ℝ P : Matrix n n ℝ) * Q.transpose := by
  simp only [RealMatrixSplit.skewAdjointPart_eq_half, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul,
    smul_sub, Matrix.smul_mul, Matrix.mul_smul]

end Rectangular

/-- Parallel addition preserves a specified common kernel vector. -/
theorem add_shared_kernel [Fintype n] (P₁ P₂ : Matrix n n ℝ) (ξ : n → ℝ)
    (h₁ : P₁ *ᵥ ξ = 0) (h₂ : P₂ *ᵥ ξ = 0) :
    (P₁ + P₂) *ᵥ ξ = 0 := by
  rw [Matrix.add_mulVec, h₁, h₂, zero_add]

/-- The native symmetric projection recovers the symmetric summand. -/
theorem selfAdjointPart_symmetric_add_skew (G Ω : Matrix n n ℝ)
    (hG : G.transpose = G) (hΩ : Ω.transpose = -Ω) :
    (selfAdjointPart ℝ (G + Ω) : Matrix n n ℝ) = G := by
  rw [RealMatrixSplit.selfAdjointPart_eq_half, Matrix.transpose_add, hG, hΩ]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- The native antisymmetric projection recovers the skew summand. -/
theorem skewAdjointPart_symmetric_add_skew (G Ω : Matrix n n ℝ)
    (hG : G.transpose = G) (hΩ : Ω.transpose = -Ω) :
    (skewAdjointPart ℝ (G + Ω) : Matrix n n ℝ) = Ω := by
  rw [RealMatrixSplit.skewAdjointPart_eq_half, Matrix.transpose_add, hG, hΩ]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.neg_apply, smul_eq_mul]
  ring

section Schur

variable [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {A : Matrix n n ℝ} {R : Matrix m m ℝ}

/-- The positive Schur precision is real symmetric. -/
theorem schur_precision_transpose (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    (coarsePrecision A R Q).transpose = coarsePrecision A R Q := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (coarsePrecision_posDef Q hA hR).isHermitian.eq

/-- Its inverse, the exact transported covariance, is also real symmetric. -/
theorem schur_covariance_transpose (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    ((coarsePrecision A R Q)⁻¹).transpose = (coarsePrecision A R Q)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, schur_precision_transpose Q hA hR]

/-- The exact bridge between Schur precision transport and skew congruence. -/
theorem schur_response_split (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (P : Matrix n n ℝ) :
    R⁻¹ + Q * (A⁻¹ + P) * Q.transpose =
      (coarsePrecision A R Q)⁻¹ + Q * P * Q.transpose := by
  rw [coarsePrecision_inv Q hA hR]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_add, Matrix.add_mul, add_assoc]

/-- The symmetric part of the full response is the Schur covariance. -/
theorem schur_response_selfAdjointPart (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    (selfAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ) =
      (coarsePrecision A R Q)⁻¹ := by
  rw [schur_response_split Q hA hR P]
  exact selfAdjointPart_symmetric_add_skew _ _
    (schur_covariance_transpose Q hA hR) (skew_congruence Q hP)

/-- The skew part of the full response is the transported fine skew operator. -/
theorem schur_response_skewAdjointPart (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ) =
      Q * P * Q.transpose := by
  rw [schur_response_split Q hA hR P]
  exact skewAdjointPart_symmetric_add_skew _ _
    (schur_covariance_transpose Q hA hR) (skew_congruence Q hP)

/-- The precision response retains its ordered noncommutative defect. -/
theorem schur_precision_normal_defect (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    (coarsePrecision A R Q + Q * P * Q.transpose).transpose *
        (coarsePrecision A R Q + Q * P * Q.transpose) -
      (coarsePrecision A R Q + Q * P * Q.transpose) *
        (coarsePrecision A R Q + Q * P * Q.transpose).transpose =
      (2 : ℝ) • (coarsePrecision A R Q * (Q * P * Q.transpose) -
        (Q * P * Q.transpose) * coarsePrecision A R Q) := by
  exact RealMatrixSplit.transpose_normal_defect_of_split
    (schur_precision_transpose Q hA hR) (skew_congruence Q hP) rfl

omit [DecidableEq m] in
/-- Transposing harmonic extension reverses the order of all three factors. -/
theorem harmonicExtension_transpose (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    (harmonicExtension A R Q).transpose = R * Q * (finePrecision A R Q)⁻¹ := by
  have hHt : (finePrecision A R Q).transpose = finePrecision A R Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (finePrecision_posDef Q hA hR).isHermitian.eq
  have hRt : R.transpose = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  simp only [harmonicExtension, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    hHt, hRt, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Harmonic skew transport preserves the precise order of all matrix factors. -/
theorem harmonic_skew_transport (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (P : Matrix n n ℝ) :
    (harmonicExtension A R Q).transpose * P * harmonicExtension A R Q =
      R * Q * (finePrecision A R Q)⁻¹ * P *
        (finePrecision A R Q)⁻¹ * Q.transpose * R := by
  rw [harmonicExtension_transpose Q hA hR]
  simp only [harmonicExtension, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Harmonic congruence is skew whenever the fine operator is skew.
This implication does not require the precision matrices to be positive. -/
theorem harmonic_transport_skew (Q : Matrix m n ℝ) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    ((harmonicExtension A R Q).transpose * P * harmonicExtension A R Q).transpose =
      -((harmonicExtension A R Q).transpose * P * harmonicExtension A R Q) := by
  simpa only [Matrix.transpose_transpose] using
    skew_congruence (harmonicExtension A R Q).transpose hP

/-- The actual skew response feeds a maximally isotropic native incidence graph. -/
theorem schur_response_incidence_orthogonal (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) :
    etaOrthogonal (incidenceSpace (matrixSharp
        (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ))) =
      (incidenceSpace (matrixSharp
        (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ)) :
          Set (PhaseSpaceCarrier (m → ℝ))) := by
  apply incidence_etaOrthogonal
  apply matrixSharp_skew
  rw [schur_response_skewAdjointPart Q hA hR hP]
  exact skew_congruence Q hP

/-- Coarse incidence pairings equal the fine skew pairing on pulled-back covectors. -/
theorem schur_response_incidence_cross_pairing (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) (ξ η : m → ℝ) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp
          (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ))
            (dotProductEquiv ℝ m ξ))
        (incidenceMap (-matrixSharp
          (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ))
            (dotProductEquiv ℝ m η)) =
      2 * ((Q.transpose *ᵥ η) ⬝ᵥ (P *ᵥ (Q.transpose *ᵥ ξ))) := by
  rw [schur_response_skewAdjointPart Q hA hR hP]
  rw [incidence_cross_pairing _ (matrixSharp_skew _ (skew_congruence Q hP)),
    matrixSharp_apply, dotProductEquiv_apply_apply]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]

/-- Pullback-kernel states are mirror fixed on the actual Schur skew graph. -/
theorem schur_response_incidence_fixed_of_pullback_kernel (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) {P : Matrix n n ℝ}
    (hP : P.transpose = -P) (ξ : m → ℝ)
    (hξ : P *ᵥ (Q.transpose *ᵥ ξ) = 0) :
    diracMirror (incidenceMap (matrixSharp
      (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ))
        (dotProductEquiv ℝ m ξ)) =
      incidenceMap (matrixSharp
        (skewAdjointPart ℝ (R⁻¹ + Q * (A⁻¹ + P) * Q.transpose) : Matrix m m ℝ))
          (dotProductEquiv ℝ m ξ) := by
  apply (diracMirror_incidence_fixed_iff _ _).mpr
  rw [matrixSharp_apply, schur_response_skewAdjointPart Q hA hR hP]
  exact congruence_kernel_transport Q P ξ hξ

end Schur

end InfoGeometry.OperatorAlgebra.DiracCoarseGraining
