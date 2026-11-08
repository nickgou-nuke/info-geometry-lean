import InfoGeometry.MassSpectrometry.SignatureCorrelationGeometry
import InfoGeometry.MassSpectrometry.FragmentationGreenResponse
import InfoGeometry.Canonical.FiniteSteinInverse

/-!
# Finite time/channel signatures and their Stein correlation matrix

The chosen column-vector readout is x ↦ C K^t x. Its row-distribution counterpart
uses a transpose and is not silently substituted. These are specified linear
readouts, not an asserted physical mass-spectrometer simulator.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.FragmentObservability
open scoped BigOperators Matrix
open SignatureGeometry
open InfoGeometry.Canonical.FiniteSteinInverse

variable {ι J : Type*} [Fintype ι] [Fintype J]

/-- Native finite Euclidean realization, with no custom inner-product carrier. -/
def matrixMap (C : Matrix J ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ J :=
  ((WithLp.linearEquiv 2 ℝ (J → ℝ)).symm.toLinearMap.comp
    ((Matrix.mulVecLin C).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap)).toContinuousLinearMap

@[simp] theorem matrixMap_apply (C : Matrix J ι ℝ) (x : EuclideanSpace ℝ ι) (j : J) :
    matrixMap C x j = ∑ i, C j i * x i := rfl

theorem matrixMap_mul {κ : Type*} [Fintype κ]
    (C : Matrix J ι ℝ) (K : Matrix ι κ ℝ) :
    matrixMap (C*K) = (matrixMap C).comp (matrixMap K) := by
  ext x j
  exact congrFun (Matrix.mulVec_mulVec (fun i => x i) C K).symm j

/-- The Euclidean adjoint is exactly matrix transposition on this real carrier. -/
theorem matrixMap_transpose (C : Matrix J ι ℝ) :
    matrixMap C.transpose = (matrixMap C).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, Real.inner_apply, matrixMap_apply,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem matrixMap_gram (C : Matrix J ι ℝ) :
    matrixMap (C.transpose*C) = gram (matrixMap C) := by
  rw [matrixMap_mul, matrixMap_transpose]
  rfl

variable [DecidableEq ι]

/-- One row for each time/channel pair. -/
def historyMatrix (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (N : ℕ) :
    Matrix (Fin N × J) ι ℝ := fun tj i => (C * K ^ tj.1.val) tj.2 i

def historyMap (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (N : ℕ) :=
  matrixMap (historyMatrix K C N)

@[simp] theorem historyMap_apply (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ)
    (N : ℕ) (x : EuclideanSpace ℝ ι) (t : Fin N) (j : J) :
    historyMap K C N x (t,j) = matrixMap (C*K^t.val) x j := rfl

def historyGram (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (N : ℕ) : Matrix ι ι ℝ :=
  (historyMatrix K C N).transpose * historyMatrix K C N

/-- Correlations of time-resolved signatures are a finite observability Gramian. -/
theorem historyGram_eq_finiteStein (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (N : ℕ) :
    historyGram K C N = finiteStein K.transpose K (C.transpose*C) N := by
  have ht (k : ℕ) : (C*K^k).transpose*(C*K^k) =
      K.transpose^k*(C.transpose*C)*K^k := by
    rw [Matrix.transpose_mul, Matrix.transpose_pow]
    simp only [Matrix.mul_assoc]
  calc
    historyGram K C N = ∑ t : Fin N, (C*K^t.val).transpose*(C*K^t.val) := by
      ext i j
      simp only [historyGram, historyMatrix, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.sum_apply, Fintype.sum_prod_type]
    _ = ∑ t : Fin N, K.transpose^t.val*(C.transpose*C)*K^t.val := by
      apply Finset.sum_congr rfl
      intro t _
      exact ht t.val
    _ = finiteStein K.transpose K (C.transpose*C) N := by
      simpa [finiteStein] using
        (Fin.sum_univ_eq_sum_range (fun k => K.transpose^k*(C.transpose*C)*K^k) N)

/-- The actual matrix correlation and the native Hilbert Gram agree. -/
theorem historyGram_realization (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ) (N : ℕ) :
    matrixMap (historyGram K C N) = gram (historyMap K C N) :=
  matrixMap_gram _

theorem historyGram_stein (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ)
    (N : ℕ) (hN : K^N=0) :
    historyGram K C N - K.transpose*historyGram K C N*K = C.transpose*C := by
  rw [historyGram_eq_finiteStein]
  exact solve_of_right_nilpotent _ _ _ _ hN

theorem historyGram_stein_unique (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ)
    (N : ℕ) (hN : K^N=0) (W : Matrix ι ι ℝ)
    (hW : W-K.transpose*W*K=C.transpose*C) : W=historyGram K C N := by
  have ht : K.transpose^N=0 := by rw [← Matrix.transpose_pow, hN]; rfl
  exact solution_unique _ _ _ _ _ N ht hW (historyGram_stein K C N hN)

/-- Same dynamics but different readouts: no positivity claim for the cross term. -/
def historyCrossGram (K : Matrix ι ι ℝ) (C D : Matrix J ι ℝ) (N : ℕ) :
    Matrix ι ι ℝ := finiteStein K.transpose K (C.transpose*D) N

/-- The finite cross-Stein sum is the actual cross-correlation of two histories. -/
theorem historyCrossGram_as_correlation (K : Matrix ι ι ℝ) (C D : Matrix J ι ℝ)
    (N : ℕ) :
    (historyMatrix K C N).transpose * historyMatrix K D N = historyCrossGram K C D N := by
  have ht (k : ℕ) : (C*K^k).transpose*(D*K^k) =
      K.transpose^k*(C.transpose*D)*K^k := by
    rw [Matrix.transpose_mul, Matrix.transpose_pow]
    simp only [Matrix.mul_assoc]
  calc
    (historyMatrix K C N).transpose * historyMatrix K D N =
        ∑ t : Fin N, (C*K^t.val).transpose*(D*K^t.val) := by
      ext i j
      simp only [historyMatrix, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.sum_apply, Fintype.sum_prod_type]
    _ = ∑ t : Fin N, K.transpose^t.val*(C.transpose*D)*K^t.val := by
      apply Finset.sum_congr rfl
      intro t _
      exact ht t.val
    _ = historyCrossGram K C D N := by
      simpa [historyCrossGram, finiteStein] using
        (Fin.sum_univ_eq_sum_range (fun k => K.transpose^k*(C.transpose*D)*K^k) N)

theorem historyCrossGram_realization (K : Matrix ι ι ℝ) (C D : Matrix J ι ℝ)
    (N : ℕ) :
    matrixMap (historyCrossGram K C D N) =
      crossGram (historyMap K C N) (historyMap K D N) := by
  rw [← historyCrossGram_as_correlation, matrixMap_mul, matrixMap_transpose]
  rfl

theorem historyCrossGram_stein (K : Matrix ι ι ℝ) (C D : Matrix J ι ℝ)
    (N : ℕ) (hN : K^N=0) :
    historyCrossGram K C D N - K.transpose*historyCrossGram K C D N*K = C.transpose*D :=
  solve_of_right_nilpotent _ _ _ _ hN

/-- Null Gram directions are absent from every time/channel readout. -/
theorem historyGram_zero_iff (K : Matrix ι ι ℝ) (C : Matrix J ι ℝ)
    (N : ℕ) (x : EuclideanSpace ℝ ι) :
    matrixMap (historyGram K C N) x = 0 ↔
      ∀ t : Fin N, matrixMap (C*K^t.val) x = 0 := by
  rw [historyGram_realization, gram_zero_iff]
  constructor
  · intro h t
    ext j
    exact congrArg (fun y : EuclideanSpace ℝ (Fin N × J) => y (t,j)) h
  · intro h
    ext tj
    exact congrArg (fun y : EuclideanSpace ℝ J => y tj.2) (h tj.1)

/-- The actual grammar supplies nilpotence via its existing rank theorem. -/
theorem grammar_historyGram_stein {n : ℕ} {D : FragmentationDAG n}
    (G : StochasticGrammar D) (C : Matrix J (Fin n) ℝ) :
    let N := InfoGeometry.Algebra.RankedMatrixPowers.rankHorizon D.rank
    historyGram G.transientMatrix C N -
      G.transientMatrix.transpose * historyGram G.transientMatrix C N * G.transientMatrix =
        C.transpose*C :=
  historyGram_stein _ _ _ G.transient_pow_rankHorizon_eq_zero

end InfoGeometry.MassSpectrometry.FragmentObservability
