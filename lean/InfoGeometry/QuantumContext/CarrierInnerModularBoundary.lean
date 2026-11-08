/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.CarrierInnerKMSBoundary

/-!
# Complex-parameter boundary for the attention carrier action

For one fixed finite attention seed, this file defines the complex exponential
conjugation on the full algebraic matrix direct-limit carrier. It proves real
parameter agreement with the existing carrier action and identifies the
`-Complex.I` boundary with conjugation by the embedded attention density and
its inverse. The selected-state KMS readback is then stated for arbitrary
carrier elements. These are algebraic identities; no analytic continuation,
holomorphicity, or completed operator-algebra assertion is made.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.CarrierInnerModularBoundary

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.CarrierInnerModularFlow
open InfoGeometry.QuantumContext.CarrierInnerKMSBoundary
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

/-- The complex exponential phase at complex parameter `z`. -/
def complexModularPhase (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) (z : ℂ) (i : Fin (2 ^ k)) : ℂ :=
  Complex.exp (Complex.I * z * (β : ℂ) * (logits i : ℂ))

/-- The diagonal complex-parameter exponential on matrix stage `k`. -/
def complexModularExponential (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) (z : ℂ) : MatrixStage k :=
  Matrix.diagonal (complexModularPhase k logits β z)

/-- Complex-parameter conjugation by the fixed stage exponential on the full
algebraic direct-limit carrier. -/
def carrierComplexModularFlow (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) (z : ℂ) (x : Carrier) : Carrier :=
  stageInjection k (complexModularExponential k logits β z) * x *
    stageInjection k (complexModularExponential k logits β (-z))

/-- Complexifying a real time parameter recovers the existing finite-stage
modular unitary. -/
theorem complexModularExponential_real (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β t : ℝ) :
    complexModularExponential k logits β (t : ℂ) = modularUnitary logits β t := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complexModularExponential, complexModularPhase, modularUnitary, modularPhase]
  · simp [complexModularExponential, modularUnitary, hij]

/-- The complex-parameter carrier conjugation restricts to the already-owned
real-time action, for every observable in the full carrier. -/
theorem carrierComplexModularFlow_real (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (x : Carrier) :
    carrierComplexModularFlow k logits β (t : ℂ) x =
      carrierModularFlow k logits β t x := by
  unfold carrierComplexModularFlow carrierModularFlow carrierModularUnitary
  rw [complexModularExponential_real]
  have hneg := complexModularExponential_real k logits β (-t)
  rw [show -((t : ℂ)) = ((-t : ℝ) : ℂ) by simp, hneg]

/-- Complex partition function written in the exponential form used at the
imaginary boundary. -/
def complexAttentionPartition (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) : ℂ :=
  ∑ i : Fin (2 ^ k), Complex.exp ((β * logits i : ℝ) : ℂ)

/-- Scalar relating the raw Boltzmann exponential to the dimension-scaled
attention density. It cancels from inner conjugation. -/
def boundaryNormalization (k : ℕ) (logits : Fin (2 ^ k) → ℝ)
    (β : ℝ) : ℂ :=
  complexAttentionPartition k logits β / (2 ^ k : ℂ)

private theorem complexAttentionPartition_eq_realSum (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    complexAttentionPartition k logits β =
      ((∑ i : Fin (2 ^ k), Real.exp (β * logits i) : ℝ) : ℂ) := by
  dsimp [complexAttentionPartition]
  simp only [← Complex.ofReal_exp]
  exact (map_sum (algebraMap ℝ ℂ)
    (fun i : Fin (2 ^ k) => Real.exp (β * logits i)) Finset.univ).symm

private theorem complexAttentionPartition_ne_zero (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    complexAttentionPartition k logits β ≠ 0 := by
  rw [complexAttentionPartition_eq_realSum]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro i hi
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨⟨0, by
      have hpow : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
      omega⟩, Finset.mem_univ _, Real.exp_pos _⟩

private theorem softmaxWeight_complex_exp (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (i : Fin (2 ^ k)) :
    (softmaxWeight logits β i : ℂ) =
      Complex.exp ((β * logits i : ℝ) : ℂ) /
        complexAttentionPartition k logits β := by
  rw [softmaxWeight, complexAttentionPartition_eq_realSum]
  simp only [Complex.ofReal_div, Complex.ofReal_exp]

/-- At the negative imaginary parameter, the exponential diagonal is a central
scalar multiple of the scaled attention density. -/
private theorem complexModularExponential_neg_I_proportional (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    complexModularExponential k logits β (-Complex.I) =
      boundaryNormalization k logits β • attentionStageDensity k logits β := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, smul_eq_mul, complexModularExponential,
      Matrix.diagonal_apply, boundaryNormalization,
      attentionStageDensity, complexModularPhase]
    simp only [ite_true]
    have hI : Complex.I * -Complex.I = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      norm_num
    have hphase : Complex.exp
        (Complex.I * -Complex.I * (β : ℂ) * (logits i : ℂ)) =
        Complex.exp ((β * logits i : ℝ) : ℂ) := by
      congr 1
      rw [hI]
      push_cast
      ring
    rw [hphase]
    rw [softmaxWeight_complex_exp]
    field_simp [complexAttentionPartition_ne_zero k logits β,
      show (2 ^ k : ℂ) ≠ 0 by
        norm_cast
        exact pow_ne_zero k (by norm_num)]
  · simp [complexModularExponential, hij,
      boundaryNormalization, attentionStageDensity]

/-- At the positive imaginary parameter, the exponential diagonal is the
reciprocal normalization times the inverse scaled attention density. -/
private theorem complexModularExponential_pos_I_proportional (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) :
    complexModularExponential k logits β Complex.I =
      (boundaryNormalization k logits β)⁻¹ •
        attentionStageDensityInv k logits β := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, smul_eq_mul, complexModularExponential,
      Matrix.diagonal_apply, boundaryNormalization,
      attentionStageDensityInv, complexModularPhase]
    simp only [ite_true]
    have hphase : Complex.exp
        (Complex.I * Complex.I * (β : ℂ) * (logits i : ℂ)) =
        Complex.exp (-((β * logits i : ℝ) : ℂ)) := by
      congr 1
      rw [Complex.I_mul_I]
      push_cast
      ring
    rw [hphase, Complex.exp_neg]
    rw [softmaxWeight_complex_exp]
    have hZ := complexAttentionPartition_ne_zero k logits β
    have hd : (2 ^ k : ℂ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero k (by norm_num)
    field_simp [hZ, hd]
  · simp [complexModularExponential, hij,
      attentionStageDensityInv]

/-- The inverse boundary normalization cancels the normalization in an inner
conjugation, in any algebra over `ℂ`. -/
private theorem scalar_conjugation_cancel {A : Type*} [Ring A] [Algebra ℂ A]
    (c : ℂ) (hc : c ≠ 0) (a b y : A) :
    (c • a) * y * (c⁻¹ • b) = a * y * b := by
  calc
    (c • a) * y * (c⁻¹ • b) = (c • (a * y)) * (c⁻¹ • b) := by
      rw [smul_mul_assoc]
    _ = c • (a * y * (c⁻¹ • b)) := by
      rw [smul_mul_assoc]
    _ = c • (c⁻¹ • (a * y * b)) := by
      apply congrArg (fun q : A => c • q)
      exact mul_smul_comm (c⁻¹) (a * y) b
    _ = a * y * b := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The complex-parameter boundary at `-Complex.I` is conjugation by the
embedded attention density and its inverse, on every carrier element. -/
theorem carrierComplexModularFlow_neg_I (k : ℕ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (y : Carrier) :
    carrierComplexModularFlow k logits β (-Complex.I) y =
      stageInjection k (attentionStageDensity k logits β) * y *
        stageInjection k (attentionStageDensityInv k logits β) := by
  unfold carrierComplexModularFlow
  simp only [neg_neg]
  rw [complexModularExponential_neg_I_proportional,
    complexModularExponential_pos_I_proportional]
  have hc : boundaryNormalization k logits β ≠ 0 := by
    dsimp [boundaryNormalization]
    exact div_ne_zero (complexAttentionPartition_ne_zero k logits β) (by
      norm_cast
      exact pow_ne_zero k (by norm_num))
  have hmap₁ : stageInjection k
      (boundaryNormalization k logits β • attentionStageDensity k logits β) =
        boundaryNormalization k logits β •
          stageInjection k (attentionStageDensity k logits β) := by
    simp only [map_smul]
  have hmap₂ : stageInjection k
      ((boundaryNormalization k logits β)⁻¹ •
        attentionStageDensityInv k logits β) =
        (boundaryNormalization k logits β)⁻¹ •
          stageInjection k (attentionStageDensityInv k logits β) := by
    simp only [map_smul]
  rw [hmap₁, hmap₂]
  exact scalar_conjugation_cancel _ hc _ _ _

/-- The selected attention colimit functional obeys the KMS boundary identity
for arbitrary full-carrier observables when the boundary is evaluated through
the complex-parameter flow. -/
theorem attentionColimitFunctional_complexFlow_kms_boundary
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ) (x y : Carrier) :
    selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (x * carrierComplexModularFlow k logits β (-Complex.I) y) =
      selectedStageColimitFunctional k (attentionStageDensity k logits β)
        (y * x) := by
  rw [carrierComplexModularFlow_neg_I]
  exact attentionColimitFunctional_carrier_kms_boundary k logits β x y

end InfoGeometry.QuantumContext.CarrierInnerModularBoundary

end
