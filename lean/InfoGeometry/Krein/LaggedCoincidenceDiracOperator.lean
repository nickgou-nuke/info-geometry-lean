import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Chiral operator for time-ordered coincidence data

For a lagged coincidence matrix `F`, the doubled operator

`D F = [[0, F], [Fᵀ, 0]]`

is symmetric even when `F` is not.  Its square keeps the source and target
Gram operators separate.  This is the finite noncommutative block-algebra
core of the time-oriented construction; no detailed-balance or stochastic
interpretation is assumed.
-/

namespace InfoGeometry.Krein

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev DoubledLaggedMatrix (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- The symmetric doubled operator associated with an oriented lagged matrix. -/
def laggedCoincidenceDirac (F : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 0 F F.transpose 0

/-- Off-diagonal observation embedding for a latent left/right factor pair. -/
def laggedFactorEmbedding (L R : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 0 L R 0

/-! ### Finite symmetric/antisymmetric nonequilibrium split -/

/-- The reversible (transpose-symmetric) part of a finite interaction matrix. -/
noncomputable def reversiblePart (W : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (W + W.transpose)

/-- The circulating (transpose-antisymmetric) part of a finite interaction matrix. -/
noncomputable def circulatingPart (W : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (W - W.transpose)

theorem reversiblePart_transpose (W : Matrix n n ℝ) :
    (reversiblePart W).transpose = reversiblePart W := by
  simp [reversiblePart, add_comm]

theorem circulatingPart_transpose (W : Matrix n n ℝ) :
    (circulatingPart W).transpose = -(circulatingPart W) := by
  simp [circulatingPart, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem reversiblePart_add_circulatingPart (W : Matrix n n ℝ) :
    reversiblePart W + circulatingPart W = W := by
  ext i j
  simp [reversiblePart, circulatingPart]
  ring

theorem reversiblePart_sub_circulatingPart (W : Matrix n n ℝ) :
    reversiblePart W - circulatingPart W = W.transpose := by
  ext i j
  simp [reversiblePart, circulatingPart]
  ring

theorem laggedCoincidenceDirac_reversible_circulating_decomposition
    (F : Matrix n n ℝ) :
    laggedCoincidenceDirac F =
      Matrix.fromBlocks (0 : Matrix n n ℝ) (reversiblePart F)
        (reversiblePart F) 0 +
      Matrix.fromBlocks (0 : Matrix n n ℝ) (circulatingPart F)
        (-(circulatingPart F)) 0 := by
  rw [laggedCoincidenceDirac]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [reversiblePart, circulatingPart] <;> ring

theorem circulatingPart_eq_zero_iff (W : Matrix n n ℝ) :
    circulatingPart W = 0 ↔ W.transpose = W := by
  constructor
  · intro h
    have hadd := reversiblePart_add_circulatingPart W
    have hsub := reversiblePart_sub_circulatingPart W
    rw [h, add_zero] at hadd
    rw [h, sub_zero] at hsub
    exact hsub.symm.trans hadd
  · intro h
    ext i j
    simp [circulatingPart, h]

/-! ### Covariance-weighted stationary current -/

/-- The covariance-weighted antisymmetric generator of a linear diffusion. -/
noncomputable def covarianceCurrent
    (M covariance : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (M * covariance - covariance * M.transpose)

theorem covarianceCurrent_transpose
    (M covariance : Matrix n n ℝ)
    (hSym : covariance.transpose = covariance) :
    (covarianceCurrent M covariance).transpose =
      -(covarianceCurrent M covariance) := by
  simp [covarianceCurrent, Matrix.transpose_mul, hSym, sub_eq_add_neg,
    smul_add, smul_neg]

theorem drift_covariance_eq_dissipation_add_current
    (M covariance D : Matrix n n ℝ)
    (hLyap : M * covariance + covariance * M.transpose + (2 : ℝ) • D = 0) :
    M * covariance = -D + covarianceCurrent M covariance := by
  rw [covarianceCurrent]
  have hcovariance : covariance * M.transpose =
      -(2 : ℝ) • D - M * covariance := by
    ext i j
    have h := congr_fun (congr_fun hLyap i) j
    simp at h ⊢
    linarith
  rw [hcovariance]
  ext i j
  simp
  ring

/-! ### Trace-normalized finite Gram readout -/

/-- The trace-normalized right Gram operator of a finite affinity matrix. -/
noncomputable def traceNormalizedGram (F : Matrix n n ℝ) : Matrix n n ℝ :=
  (Matrix.trace (F.transpose * F))⁻¹ • (F.transpose * F)

/-- The trace-normalized left Gram operator of a finite affinity matrix. -/
noncomputable def traceNormalizedLeftGram (F : Matrix n n ℝ) : Matrix n n ℝ :=
  (Matrix.trace (F * F.transpose))⁻¹ • (F * F.transpose)

theorem trace_traceNormalizedGram
    (F : Matrix n n ℝ)
    (htrace : Matrix.trace (F.transpose * F) ≠ 0) :
    Matrix.trace (traceNormalizedGram F) = 1 := by
  rw [traceNormalizedGram, Matrix.trace_smul]
  exact inv_mul_cancel₀ htrace

theorem trace_gram_nonneg (F : Matrix n n ℝ) :
    0 ≤ Matrix.trace (F.transpose * F) := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intro i hi
  change 0 ≤ (F.transpose * F) i i
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k hk => mul_self_nonneg (F k i))

theorem trace_gram_ne_zero_of_ne_zero {F : Matrix n n ℝ} (hF : F ≠ 0) :
    Matrix.trace (F.transpose * F) ≠ 0 := by
  intro hzero
  have hsum : ∑ i : n, ∑ j : n, (F j i) ^ 2 = 0 := by
    have htrace := hzero
    rw [Matrix.trace] at htrace
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using htrace
  have hrows :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => Finset.sum_nonneg fun j hj => sq_nonneg (F j i))).mp hsum
  apply hF
  funext i j
  have hrow : ∑ k : n, (F k j) ^ 2 = 0 := congrFun hrows j
  exact sq_eq_zero_iff.mp
    (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg
        (fun k => sq_nonneg (F k j))).mp hrow) i)

theorem traceNormalizedGram_scale_invariant
    (F : Matrix n n ℝ) (α : ℝ) (hα : α ≠ 0) :
    traceNormalizedGram (α • F) = traceNormalizedGram F := by
  by_cases hF : F = 0
  · subst F
    simp [traceNormalizedGram]
  unfold traceNormalizedGram
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.trace_smul]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hT : Matrix.trace (F.transpose * F) ≠ 0 :=
    trace_gram_ne_zero_of_ne_zero hF
  rw [show (α • (F.transpose * F)).trace =
      α * (F.transpose * F).trace by simp [Matrix.trace_smul, smul_eq_mul]]
  field_simp [hα, hT]

theorem traceNormalizedLeftGram_scale_invariant
    (F : Matrix n n ℝ) (α : ℝ) (hα : α ≠ 0) :
    traceNormalizedLeftGram (α • F) = traceNormalizedLeftGram F := by
  by_cases hF : F = 0
  · subst F
    simp [traceNormalizedLeftGram]
  unfold traceNormalizedLeftGram
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.trace_smul]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hT : Matrix.trace (F * F.transpose) ≠ 0 := by
    rw [Matrix.trace_mul_comm]
    exact trace_gram_ne_zero_of_ne_zero hF
  rw [show (α • (F * F.transpose)).trace =
      α * (F * F.transpose).trace by simp [Matrix.trace_smul, smul_eq_mul]]
  field_simp [hα, hT]

theorem trace_traceNormalizedGram_of_ne_zero
    {F : Matrix n n ℝ} (hF : F ≠ 0) :
    Matrix.trace (traceNormalizedGram F) = 1 := by
  exact trace_traceNormalizedGram F (trace_gram_ne_zero_of_ne_zero hF)

theorem trace_gram_eq_trace_leftGram (F : Matrix n n ℝ) :
    Matrix.trace (F.transpose * F) = Matrix.trace (F * F.transpose) := by
  exact Matrix.trace_mul_comm F.transpose F

theorem traceNormalizedLeftGram_eq_common_denominator (F : Matrix n n ℝ) :
    traceNormalizedLeftGram F =
      (Matrix.trace (F.transpose * F))⁻¹ • (F * F.transpose) := by
  unfold traceNormalizedLeftGram
  rw [trace_gram_eq_trace_leftGram]

theorem traceNormalizedGram_transpose (F : Matrix n n ℝ) :
    (traceNormalizedGram F).transpose = traceNormalizedGram F := by
  simp [traceNormalizedGram, Matrix.transpose_mul]

theorem trace_traceNormalizedLeftGram
    (F : Matrix n n ℝ)
    (htrace : Matrix.trace (F * F.transpose) ≠ 0) :
    Matrix.trace (traceNormalizedLeftGram F) = 1 := by
  rw [traceNormalizedLeftGram, Matrix.trace_smul]
  exact inv_mul_cancel₀ htrace

theorem trace_leftGram_nonneg (F : Matrix n n ℝ) :
    0 ≤ Matrix.trace (F * F.transpose) := by
  simpa only [Matrix.transpose_transpose] using trace_gram_nonneg F.transpose

theorem trace_traceNormalizedLeftGram_of_right_ne_zero
    (F : Matrix n n ℝ)
    (htrace : Matrix.trace (F.transpose * F) ≠ 0) :
    Matrix.trace (traceNormalizedLeftGram F) = 1 := by
  apply trace_traceNormalizedLeftGram F
  rw [← trace_gram_eq_trace_leftGram F]
  exact htrace

theorem trace_traceNormalizedLeftGram_of_ne_zero
    {F : Matrix n n ℝ} (hF : F ≠ 0) :
    Matrix.trace (traceNormalizedLeftGram F) = 1 := by
  exact trace_traceNormalizedLeftGram_of_right_ne_zero F
    (trace_gram_ne_zero_of_ne_zero hF)

theorem traceNormalizedLeftGram_transpose (F : Matrix n n ℝ) :
    (traceNormalizedLeftGram F).transpose = traceNormalizedLeftGram F := by
  simp [traceNormalizedLeftGram, Matrix.transpose_mul]

theorem laggedCoincidenceDirac_triFactor_congruence
    (L S R : Matrix n n ℝ) :
    laggedCoincidenceDirac (L * S.transpose * R.transpose) =
        laggedFactorEmbedding L R * laggedCoincidenceDirac S *
        (laggedFactorEmbedding L R).transpose := by
  simp [laggedCoincidenceDirac, laggedFactorEmbedding,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
    Matrix.mul_assoc]

/-- The source/target grading on the doubled carrier. -/
def laggedCoincidenceGrading : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 1 0 0 (-1)

theorem laggedCoincidenceDirac_transpose (F : Matrix n n ℝ) :
    (laggedCoincidenceDirac F).transpose = laggedCoincidenceDirac F := by
  simp [laggedCoincidenceDirac, Matrix.fromBlocks_transpose]

theorem laggedCoincidenceDirac_square (F : Matrix n n ℝ) :
    laggedCoincidenceDirac F * laggedCoincidenceDirac F =
      Matrix.fromBlocks (F * F.transpose) 0 0 (F.transpose * F) := by
  rw [laggedCoincidenceDirac, Matrix.fromBlocks_multiply]
  simp

theorem trace_laggedCoincidenceDirac_square (F : Matrix n n ℝ) :
    Matrix.trace (laggedCoincidenceDirac F * laggedCoincidenceDirac F) =
      2 * Matrix.trace (F.transpose * F) := by
  rw [laggedCoincidenceDirac_square]
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks]
  have htrace :
      (∑ i : n, (F * F.transpose) i i) =
        ∑ i : n, (F.transpose * F) i i := by
    simpa only [Matrix.trace] using Matrix.trace_mul_comm F F.transpose
  rw [htrace]
  ring

theorem trace_laggedCoincidenceDirac_square_nonneg (F : Matrix n n ℝ) :
    0 ≤ Matrix.trace (laggedCoincidenceDirac F * laggedCoincidenceDirac F) := by
  rw [trace_laggedCoincidenceDirac_square]
  exact mul_nonneg (by norm_num) (trace_gram_nonneg F)

/-! ### Finite Tomita sheet-swap compatibility -/

/-- The source/target sheet swap on the doubled lagged carrier. -/
def laggedCoincidenceSwap : DoubledLaggedMatrix n :=
  Matrix.fromBlocks 0 1 1 0

theorem laggedCoincidenceSwap_square :
    laggedCoincidenceSwap (n := n) * laggedCoincidenceSwap (n := n) = 1 := by
  rw [laggedCoincidenceSwap, Matrix.fromBlocks_multiply]
  simp

theorem laggedCoincidenceSwap_conjugates_transpose (F : Matrix n n ℝ) :
    laggedCoincidenceSwap (n := n) * laggedCoincidenceDirac F *
        laggedCoincidenceSwap (n := n) =
      laggedCoincidenceDirac F.transpose := by
  rw [laggedCoincidenceSwap, laggedCoincidenceDirac,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [laggedCoincidenceDirac]

theorem laggedCoincidenceSwap_conjugates_square (F : Matrix n n ℝ) :
    laggedCoincidenceSwap (n := n) *
        (laggedCoincidenceDirac F * laggedCoincidenceDirac F) *
        laggedCoincidenceSwap (n := n) =
      Matrix.fromBlocks (F.transpose * F) 0 0 (F * F.transpose) := by
  rw [laggedCoincidenceDirac_square, laggedCoincidenceSwap,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.transpose_transpose]

theorem laggedCoincidenceGrading_square :
    laggedCoincidenceGrading (n := n) * laggedCoincidenceGrading (n := n) = 1 := by
  rw [laggedCoincidenceGrading, Matrix.fromBlocks_multiply]
  simp

theorem laggedCoincidenceGrading_anticommutes (F : Matrix n n ℝ) :
    laggedCoincidenceGrading (n := n) * laggedCoincidenceDirac F =
      -(laggedCoincidenceDirac F * laggedCoincidenceGrading (n := n)) := by
  rw [laggedCoincidenceGrading, laggedCoincidenceDirac,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

end InfoGeometry.Krein
