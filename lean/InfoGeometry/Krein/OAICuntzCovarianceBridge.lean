import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock
import OAI.Analysis.Cuntz.State

/-!
# OAI Cuntz-matrix bridge for finite covariance projections

The local covariance projection is a concrete positive matrix. This adapter
packages that matrix in OAI's finite-matrix Cuntz carrier and then passes to its
Cuntz monoid. The scalar covariance parameter and its trace remain explicit;
the Cuntz class alone does not encode a Born probability.
-/

noncomputable section

open scoped Matrix CStarAlgebra

namespace InfoGeometry.Krein.OAICuntzCovarianceBridge

open FiniteCovarianceMajoranaBlock

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- A rank-one square root factor for the two-dimensional covariance projection. -/
def covarianceFactor (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt c, Real.sqrt (1 - c); 0, 0]

/-- The real covariance projection viewed as a complex matrix. -/
def covarianceComplexMatrix (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (covarianceProjection c).map Complex.ofReal

/-- Complex Gram factor corresponding to `covarianceFactor`. -/
def covarianceComplexFactor (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (covarianceFactor c).map Complex.ofReal

/-- The one-column vector whose cross-Gram is the covariance projection. -/
def covarianceColumn (c : ℝ) : Matrix (Fin 2) (Fin 1) ℂ := fun i _ =>
  match i with
  | 0 => Complex.ofReal (Real.sqrt c)
  | 1 => Complex.ofReal (Real.sqrt (1 - c))

/-- The covariance projection is the Gram matrix of its explicit finite factor. -/
theorem covarianceComplexMatrix_eq_factorGram {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    covarianceComplexMatrix c = (covarianceComplexFactor c)ᴴ * covarianceComplexFactor c := by
  have hsqrtc : Complex.ofReal (Real.sqrt c) * Complex.ofReal (Real.sqrt c) =
      Complex.ofReal c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hsqrtone : Complex.ofReal (Real.sqrt (1 - c)) *
      Complex.ofReal (Real.sqrt (1 - c)) = Complex.ofReal (1 - c) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hc1)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covarianceComplexMatrix, covarianceComplexFactor, covarianceFactor,
      covarianceProjection, Matrix.mul_apply, Fin.sum_univ_succ,
      hsqrtc, hsqrtone] <;> ring

/-- Cross-Gram realization of the covariance projection by a single column. -/
theorem covarianceComplexMatrix_eq_crossGram {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    covarianceComplexMatrix c = covarianceColumn c * (covarianceColumn c)ᴴ := by
  have hsqrtc := Real.mul_self_sqrt hc
  have hsqrtone := Real.mul_self_sqrt (sub_nonneg.mpr hc1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covarianceComplexMatrix, covarianceColumn, covarianceProjection,
      Matrix.mul_apply, Fin.sum_univ_succ, ← Complex.ofReal_mul, hsqrtc, hsqrtone] <;> ring

/-- The local positive covariance matrix is positive in OAI's C⋆ matrix order. -/
theorem covarianceProjection_cstar_nonneg {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ CStarMatrix.ofMatrix (covarianceComplexMatrix c) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin 2) (Fin 2) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    CStarAlgebra.instNonnegSpectrumClass'
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨CStarMatrix.ofMatrix (covarianceComplexFactor c), ?_⟩
  change covarianceComplexMatrix c = (covarianceComplexFactor c)ᴴ * covarianceComplexFactor c
  exact covarianceComplexMatrix_eq_factorGram hc hc1

/-- Matrix form of the Krein-Dirac conjugation `A ↦ J Aᴴ J`. -/
def covarianceKreinDiracConjugate (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :=
  fundamentalSymmetry c * Aᴴ * fundamentalSymmetry c

/-- The covariance projector is fixed by Krein-Dirac conjugation. -/
theorem covarianceProjection_kreinDirac_fixed {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    covarianceKreinDiracConjugate c (covarianceProjection c) = covarianceProjection c := by
  have hP := covarianceProjection_sq hc hc1
  have hJP : fundamentalSymmetry c * covarianceProjection c = covarianceProjection c := by
    dsimp [fundamentalSymmetry]
    rw [sub_mul, Matrix.smul_mul, one_mul, hP]
    module
  have hPJ : covarianceProjection c * fundamentalSymmetry c = covarianceProjection c := by
    dsimp [fundamentalSymmetry]
    rw [mul_sub, Matrix.mul_smul, mul_one, hP]
    module
  change fundamentalSymmetry c * (covarianceProjection c).transpose *
      fundamentalSymmetry c = covarianceProjection c
  rw [covarianceProjection_self_adjoint, hJP, hPJ]

/-- The local covariance projection as an actual positive finite matrix in OAI's carrier. -/
def covarianceCuntzPositiveMatrix (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    OAI.Kaplansky.CuntzPositiveMatrix ℂ :=
  ⟨2, covarianceComplexMatrix c, covarianceProjection_cstar_nonneg hc hc1⟩

@[simp]
theorem covarianceCuntzPositiveMatrix_size (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (covarianceCuntzPositiveMatrix c hc hc1).size = 2 := rfl

@[simp]
theorem covarianceCuntzPositiveMatrix_matrix (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (covarianceCuntzPositiveMatrix c hc hc1).matrix = covarianceComplexMatrix c := rfl

/-- The resulting OAI Cuntz class, with the covariance parameter retained as input data. -/
def covarianceCuntzClass (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    OAI.Kaplansky.CuntzMonoid ℂ :=
  OAI.Kaplansky.cuntzClass (covarianceCuntzPositiveMatrix c hc hc1)

/-- The finite covariance representative retains its unit-trace observable. -/
theorem covarianceCuntzRepresentative_trace (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (Matrix.trace (covarianceCuntzPositiveMatrix c hc hc1).matrix).re = 1 := by
  change (Matrix.trace (covarianceComplexMatrix c)).re = 1
  rw [Matrix.trace_fin_two (covarianceComplexMatrix c)]
  simp [covarianceComplexMatrix, covarianceProjection]

/-- The covariance projection is Cuntz-equivalent to the one-dimensional unit.
The rectangular witnesses are the covariance column and its adjoint. -/
theorem covarianceCuntzEquivalent_unit (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    OAI.Kaplansky.CuntzEquivalent (covarianceComplexMatrix c)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  let v := covarianceColumn c
  have hp : covarianceComplexMatrix c = v * vᴴ :=
    covarianceComplexMatrix_eq_crossGram hc hc1
  have hv : vᴴ * v = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    have hsum := Real.mul_self_sqrt hc
    have hsum' := Real.mul_self_sqrt (sub_nonneg.mpr hc1)
    simp [v, covarianceColumn, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, hsum, hsum']
  constructor
  · rw [hp]
    simpa using (OAI.Kaplansky.CuntzLE.exact
      (1 : Matrix (Fin 1) (Fin 1) ℂ) v)
  · have hback : vᴴ * covarianceComplexMatrix c * v =
        (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [hp]
      calc
        (vᴴ * (v * vᴴ)) * v = vᴴ * (v * (vᴴ * v)) := by
          simp only [Matrix.mul_assoc]
        _ = vᴴ * (v * (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by rw [hv]
        _ = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by rw [Matrix.mul_one, hv]
    have h := OAI.Kaplansky.CuntzLE.exact (covarianceComplexMatrix c) vᴴ
    have h' : OAI.Kaplansky.CuntzLE (vᴴ * covarianceComplexMatrix c * v)
        (covarianceComplexMatrix c) := by
      simpa using h
    exact OAI.Kaplansky.CuntzLE.of_eq hback.symm rfl h'

/-- The OAI Cuntz class of the covariance state is the unit class. -/
theorem covarianceCuntzClass_eq_unit (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    covarianceCuntzClass c hc hc1 = OAI.Kaplansky.cuntzUnit ℂ 1 := by
  apply (OAI.Kaplansky.cuntzClass_eq _ _).mpr
  exact covarianceCuntzEquivalent_unit c hc hc1

/-- OAI's normalized dimension state reads the same unit value as the local
unit-trace covariance representative. -/
theorem covarianceCuntzDimensionState_value (d : OAI.Kaplansky.CuntzDimensionState ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    d.value (covarianceCuntzPositiveMatrix c hc hc1) = 1 := by
  calc
    d.value (covarianceCuntzPositiveMatrix c hc hc1) = d.value (.unit 1) :=
      d.value_eq (covarianceCuntzEquivalent_unit c hc hc1)
    _ = (1 : ℝ) := by simpa using d.value_unit 1

end InfoGeometry.Krein.OAICuntzCovarianceBridge

end
