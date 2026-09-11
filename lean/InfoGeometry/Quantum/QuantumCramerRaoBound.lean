import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Quantum Cramér-Rao Bound (QCRB) via Symmetric Logarithmic Derivative (SLD)

Formalizes the Quantum Cramér-Rao Bound:
  `Var_ρ(O) * g_SLD(ρ, L) ≥ (d⟨O⟩/dθ)²`
for arbitrary quantum observables `O` and density matrices `ρ = Rᵀ * R`
via Cauchy-Schwarz on the factorized Frobenius pairing with zero sorrys and zero axioms.
-/

namespace InfoGeometry.Quantum.QuantumCramerRaoBound

open Matrix
open BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! =========================================================================
    1. Frobenius Inner Product and Cauchy-Schwarz Inequality
    ========================================================================= -/

/-- Frobenius / Hilbert-Schmidt inner product on real matrices: `⟨X, Y⟩ = Tr(Xᵀ * Y)`. -/
def frobInner (X Y : Matrix n n ℝ) : ℝ :=
  Matrix.trace (Xᵀ * Y)

/-- Frobenius norm squared: `‖X‖² = Tr(Xᵀ * X)`. -/
def frobNormSq (X : Matrix n n ℝ) : ℝ :=
  frobInner X X

/-- Non-negativity of the Frobenius norm squared: `Tr(Mᵀ * M) = ∑ M_{ji}² ≥ 0`. -/
theorem frobNormSq_nonneg (M : Matrix n n ℝ) :
    0 ≤ frobNormSq M := by
  dsimp [frobNormSq, frobInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have hsq : M j i * M j i = (M j i) ^ 2 := by ring
  rw [hsq]
  exact sq_nonneg (M j i)

/-- Frobenius inner product is symmetric: `Tr(Xᵀ * Y) = Tr(Yᵀ * X)`. -/
theorem frobInner_symm (X Y : Matrix n n ℝ) :
    frobInner X Y = frobInner Y X := by
  dsimp [frobInner]
  have h_tr : Matrix.trace (Xᵀ * Y) = Matrix.trace (Xᵀ * Y)ᵀ := by
    rw [Matrix.trace_transpose]
  rw [h_tr, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Binomial expansion of the Frobenius norm squared under linear combinations. -/
theorem frobNormSq_lincomb (a b : ℝ) (X Y : Matrix n n ℝ) :
    frobNormSq (a • X + b • Y) =
      a ^ 2 * frobNormSq X + 2 * a * b * frobInner X Y + b ^ 2 * frobNormSq Y := by
  dsimp [frobNormSq, frobInner]
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  have h_symm : (Yᵀ * X).trace = (Xᵀ * Y).trace := by
    have := frobInner_symm Y X
    dsimp [frobInner] at this
    exact this
  rw [h_symm]
  ring

/--
THEOREM (Cauchy-Schwarz Inequality for Matrix Frobenius Product):
  `⟨X, Y⟩² ≤ ‖X‖² * ‖Y‖²`
-/
theorem frob_cauchy_schwarz (X Y : Matrix n n ℝ) :
    (frobInner X Y) ^ 2 ≤ (frobNormSq X) * (frobNormSq Y) := by
  have h_exp (a b : ℝ) : 0 ≤ a ^ 2 * frobNormSq X + 2 * a * b * frobInner X Y + b ^ 2 * frobNormSq Y := by
    have h := frobNormSq_nonneg (a • X + b • Y)
    rw [frobNormSq_lincomb] at h
    exact h
  by_cases hC : frobNormSq Y = 0
  · by_cases hA : frobNormSq X = 0
    · have h1 := h_exp 1 1
      have h2 := h_exp 1 (-1)
      have hB : frobInner X Y = 0 := by
        nlinarith [h1, h2, hA, hC]
      rw [hB, hA, hC]
      linarith
    · have h_pos : 0 < frobNormSq X := lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hA)
      have h1 := h_exp (frobInner X Y) (-frobNormSq X)
      rw [hC] at h1
      have hB : (frobInner X Y) ^ 2 ≤ 0 := by
        nlinarith [h1, h_pos]
      have h_sq_nonneg : 0 ≤ (frobInner X Y) ^ 2 := sq_nonneg (frobInner X Y)
      have hB_zero : (frobInner X Y) ^ 2 = 0 := le_antisymm hB h_sq_nonneg
      rw [hB_zero, hC, mul_zero]
  · have h_pos : 0 < frobNormSq Y := lt_of_le_of_ne (frobNormSq_nonneg Y) (Ne.symm hC)
    have h1 := h_exp (frobNormSq Y) (-frobInner X Y)
    have h_factor : (frobNormSq Y) ^ 2 * frobNormSq X + 2 * (frobNormSq Y) * (-frobInner X Y) * frobInner X Y + (-frobInner X Y) ^ 2 * frobNormSq Y =
        (frobNormSq Y) * (frobNormSq X * frobNormSq Y - (frobInner X Y) ^ 2) := by ring
    rw [h_factor] at h1
    nlinarith [h1, h_pos]

/-! =========================================================================
    2. Quantum State, Observable Variance, and SLD Fisher Metric
    ========================================================================= -/

/-- Expectation value of observable `O` under state `ρ`: `⟨O⟩_ρ = Tr(ρ * O)`. -/
def expectation (rho O : Matrix n n ℝ) : ℝ :=
  Matrix.trace (rho * O)

/-- Centered observable: `ΔO = O - ⟨O⟩_ρ • I`. -/
def centeredObservable (rho O : Matrix n n ℝ) : Matrix n n ℝ :=
  O - (expectation rho O) • (1 : Matrix n n ℝ)

/-- Quantum variance: `Var_ρ(O) = Tr(ρ * (ΔO)²)`. -/
def quantumVariance (rho O : Matrix n n ℝ) : ℝ :=
  Matrix.trace (rho * (centeredObservable rho O * centeredObservable rho O))

/-- Symmetric Logarithmic Derivative (SLD) operator equation: `2 • D(ρ) = L * ρ + ρ * L`. -/
def isSLD (rho drho L : Matrix n n ℝ) : Prop :=
  (2 : ℝ) • drho = L * rho + rho * L

/-- Bures-Helstrom / SLD Quantum Fisher Information: `g_SLD(ρ, L) = Tr(ρ * L²)`. -/
def sldFisherInfo (rho L : Matrix n n ℝ) : ℝ :=
  Matrix.trace (rho * (L * L))

/-- Sensitivity / expectation parameter derivative: `d⟨O⟩/dθ = Tr(D(ρ) * O)`. -/
def paramDeriv (drho O : Matrix n n ℝ) : ℝ :=
  Matrix.trace (drho * O)

/-! =========================================================================
    3. Factorized State Reduction Lemmas
    ========================================================================= -/

/--
LEMMA: Frobenius norm of a right-multiplied factor `M * Rᵀ` equals `Tr(Rᵀ * R * M²)`.
-/
theorem frobNormSq_mul_transpose (R M : Matrix n n ℝ) (hM : Mᵀ = M) :
    frobNormSq (M * Rᵀ) = Matrix.trace ((Rᵀ * R) * (M * M)) := by
  dsimp [frobNormSq, frobInner]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, hM]
  calc
    Matrix.trace ((R * M) * (M * Rᵀ))
      = Matrix.trace (R * (M * (M * Rᵀ))) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (R * (M * M * Rᵀ)) := by rw [Matrix.mul_assoc M M Rᵀ]
    _ = Matrix.trace ((M * M * Rᵀ) * R) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (M * M * (Rᵀ * R)) := by rw [Matrix.mul_assoc (M * M) Rᵀ R]
    _ = Matrix.trace ((Rᵀ * R) * (M * M)) := by rw [Matrix.trace_mul_comm]

/--
LEMMA: Frobenius pairing of symmetric operators factorizes over `ρ = Rᵀ * R`.
-/
theorem frobInner_mul_transpose (R M N : Matrix n n ℝ) (hM : Mᵀ = M) :
    frobInner (M * Rᵀ) (N * Rᵀ) = Matrix.trace ((Rᵀ * R) * (M * N)) := by
  dsimp [frobInner]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, hM]
  calc
    Matrix.trace ((R * M) * (N * Rᵀ))
      = Matrix.trace (R * (M * (N * Rᵀ))) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (R * (M * N * Rᵀ)) := by rw [Matrix.mul_assoc M N Rᵀ]
    _ = Matrix.trace ((M * N * Rᵀ) * R) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (M * N * (Rᵀ * R)) := by rw [Matrix.mul_assoc (M * N) Rᵀ R]
    _ = Matrix.trace ((Rᵀ * R) * (M * N)) := by rw [Matrix.trace_mul_comm]

/--
LEMMA: Trace duality between the SLD anti-commutator and the centered observable.
-/
theorem sld_trace_pairing (rho drho L O_tilde : Matrix n n ℝ)
    (h_sld : isSLD rho drho L)
    (h_symm : Matrix.trace (rho * (L * O_tilde)) = Matrix.trace (rho * (O_tilde * L))) :
    Matrix.trace (rho * (L * O_tilde)) = Matrix.trace (drho * O_tilde) := by
  dsimp [isSLD] at h_sld
  have h_add : Matrix.trace ((L * rho + rho * L) * O_tilde) =
      2 * Matrix.trace (rho * (L * O_tilde)) := by
    rw [Matrix.add_mul, Matrix.trace_add]
    have h1 : Matrix.trace (L * rho * O_tilde) = Matrix.trace (rho * (O_tilde * L)) := by
      calc
        Matrix.trace (L * rho * O_tilde) = Matrix.trace (L * (rho * O_tilde)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace ((rho * O_tilde) * L) := by rw [Matrix.trace_mul_comm]
        _ = Matrix.trace (rho * (O_tilde * L)) := by rw [Matrix.mul_assoc]
    have h2 : Matrix.trace (rho * L * O_tilde) = Matrix.trace (rho * (L * O_tilde)) := by
      rw [Matrix.mul_assoc]
    rw [h1, h2, h_symm]
    ring
  have h_drho : Matrix.trace ((L * rho + rho * L) * O_tilde) =
      2 * Matrix.trace (drho * O_tilde) := by
    calc
      Matrix.trace ((L * rho + rho * L) * O_tilde)
        = Matrix.trace (((2 : ℝ) • drho) * O_tilde) := by rw [← h_sld]
      _ = Matrix.trace ((2 : ℝ) • (drho * O_tilde)) := by rw [Matrix.smul_mul]
      _ = (2 : ℝ) * Matrix.trace (drho * O_tilde) := by rw [Matrix.trace_smul, smul_eq_mul]
  linarith

/-! =========================================================================
    4. The Quantum Cramér-Rao Bound (QCRB) Theorem
    ========================================================================= -/

/--
MAIN THEOREM (Quantum Cramér-Rao Bound):
For any positive semi-definite state `ρ = Rᵀ * R`, self-adjoint observable `O`,
and self-adjoint SLD operator `L`, the product of the quantum variance and
the SLD Fisher information is bounded below by the squared parameter derivative:
  `Var_ρ(O) * g_SLD(ρ, L) ≥ (d⟨O⟩/dθ)²`
-/
theorem quantum_cramer_rao_bound
    (R drho L O : Matrix n n ℝ)
    (hL : Lᵀ = L)
    (hO : Oᵀ = O)
    (h_tr_drho : Matrix.trace drho = 0)
    (h_sld : isSLD (Rᵀ * R) drho L)
    (h_symm : Matrix.trace ((Rᵀ * R) * (L * centeredObservable (Rᵀ * R) O)) =
              Matrix.trace ((Rᵀ * R) * (centeredObservable (Rᵀ * R) O * L))) :
    (paramDeriv drho O) ^ 2 ≤
      quantumVariance (Rᵀ * R) O * sldFisherInfo (Rᵀ * R) L := by
  set rho := Rᵀ * R
  set O_tilde := centeredObservable rho O
  have h_O_tilde_symm : O_tildeᵀ = O_tilde := by
    dsimp [O_tilde, centeredObservable]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hO]
  -- Construct Hilbert-Schmidt vectors X = O_tilde * Rᵀ and Y = L * Rᵀ
  set X := O_tilde * Rᵀ
  set Y := L * Rᵀ
  have h_normX : frobNormSq X = quantumVariance rho O := by
    dsimp [quantumVariance]
    exact frobNormSq_mul_transpose R O_tilde h_O_tilde_symm
  have h_normY : frobNormSq Y = sldFisherInfo rho L := by
    dsimp [sldFisherInfo]
    exact frobNormSq_mul_transpose R L hL
  have h_inner : frobInner Y X = paramDeriv drho O := by
    rw [frobInner_mul_transpose R L O_tilde hL]
    have h_pair := sld_trace_pairing rho drho L O_tilde h_sld h_symm
    rw [h_pair]
    dsimp [paramDeriv, O_tilde, centeredObservable]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    rw [Matrix.trace_sub, Matrix.trace_smul, h_tr_drho, smul_zero, sub_zero]
  have h_cs := frob_cauchy_schwarz Y X
  rw [h_inner, h_normX, h_normY, mul_comm] at h_cs
  exact h_cs

/-! =========================================================================
    5. Lower-bound form of the QCRB
    ========================================================================= -/

/--
The product form of the QCRB yields the usual variance lower bound whenever
the SLD Fisher information is strictly positive.  The sensitivity is kept
explicit: no unit-sensitivity normalization is implicit in this statement.
-/
theorem quantum_cramer_rao_variance_lower_bound
    (R drho L O : Matrix n n ℝ)
    (hL : Lᵀ = L)
    (hO : Oᵀ = O)
    (h_tr_drho : Matrix.trace drho = 0)
    (h_sld : isSLD (Rᵀ * R) drho L)
    (h_symm : Matrix.trace ((Rᵀ * R) * (L * centeredObservable (Rᵀ * R) O)) =
              Matrix.trace ((Rᵀ * R) * (centeredObservable (Rᵀ * R) O * L)))
    (h_fisher_pos : 0 < sldFisherInfo (Rᵀ * R) L) :
    (paramDeriv drho O) ^ 2 / sldFisherInfo (Rᵀ * R) L ≤
      quantumVariance (Rᵀ * R) O := by
  have h_product := quantum_cramer_rao_bound R drho L O hL hO h_tr_drho h_sld h_symm
  have h_inv_pos : 0 < (sldFisherInfo (Rᵀ * R) L)⁻¹ :=
    inv_pos.mpr h_fisher_pos
  calc
    (paramDeriv drho O) ^ 2 / sldFisherInfo (Rᵀ * R) L =
        (paramDeriv drho O) ^ 2 * (sldFisherInfo (Rᵀ * R) L)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ (quantumVariance (Rᵀ * R) O * sldFisherInfo (Rᵀ * R) L) *
          (sldFisherInfo (Rᵀ * R) L)⁻¹ := by
          exact mul_le_mul_of_nonneg_right h_product (le_of_lt h_inv_pos)
    _ = quantumVariance (Rᵀ * R) O := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h_fisher_pos), mul_one]

end InfoGeometry.Quantum.QuantumCramerRaoBound
