import InfoGeometry.MassSpectrometry.SpectralOperatorSynthesis

/-! # Concrete boundary fixtures: temporal visibility, aggregation loss, and nonnormality -/
noncomputable section
namespace InfoGeometry.MassSpectrometry.SignatureOperatorAudit
open scoped BigOperators Matrix
open FragmentObservability SignatureGeometry
open InfoGeometry.Canonical.FiniteSteinInverse

/-- A two-step transient signal; this is an algebraic test, not a chemistry simulator. -/
def shift : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def detector : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
def otherDetector : Matrix (Fin 1) (Fin 2) ℝ := !![0, 1]

theorem shift_sq : shift^2=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem instant_gram : detector.transpose*detector=!![1,0;0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [detector, Matrix.mul_apply, Fin.sum_univ_one]

/-- Time resolution recovers the direction absent from the instantaneous detector. -/
theorem history_gram_identity : historyGram shift detector 2 = 1 := by
  rw [historyGram_eq_finiteStein]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [finiteStein, Finset.sum_range_succ, shift, detector,
      pow_succ, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_one, Fin.sum_univ_two]

theorem instantaneous_hidden_direction :
    gram (matrixMap detector) !₂[0,1]=0 := by
  rw [gram_zero_iff]
  ext j
  fin_cases j
  norm_num [matrixMap_apply, detector, Fin.sum_univ_two]

/-- The same direction is no longer hidden in the two-time signature. -/
theorem temporal_direction_visible :
    gram (historyMap shift detector 2) !₂[0,1] ≠ 0 := by
  rw [← historyGram_realization, history_gram_identity]
  intro h
  have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
  norm_num [matrixMap_apply, Matrix.one_apply, Fin.sum_univ_two] at hh

/-- An aggregate can cancel a signed difference even when the time-resolved Gram is full rank. -/
theorem aggregate_loses_direction :
    (detector*(1+shift)) *ᵥ ![1,-1] = 0 := by
  ext j
  fin_cases j
  norm_num [detector, shift, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_two]

theorem history_retains_aggregate_null_direction :
    historyMatrix shift detector 2 *ᵥ ![1,-1] ≠ 0 := by
  intro h
  have hh := congrFun h ((0 : Fin 2),(0 : Fin 1))
  norm_num [historyMatrix, detector, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_two] at hh

/-- Unlike a Gram matrix, a cross-Gram need not be symmetric. -/
theorem cross_gram_is_shift : detector.transpose*otherDetector=shift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [detector, otherDetector, shift, Matrix.mul_apply, Fin.sum_univ_one]

theorem cross_gram_not_symmetric :
    (detector.transpose*otherDetector).transpose ≠ detector.transpose*otherDetector := by
  rw [cross_gram_is_shift]
  intro h
  have hh := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [shift] at hh

/-- The absorbing Drazin projector is not automatically an orthogonal projector. -/
theorem absorption_projector_not_symmetric :
    (absorptionProjection 1).transpose ≠ absorptionProjection 1 := by
  intro h
  have hh := congrFun (congrFun h (some (0 : Fin 1))) none
  norm_num [absorptionProjection, Matrix.transpose_apply] at hh

theorem shift_not_unit : ¬ IsUnit shift :=
  SignatureCyclotomic.nilpotent_not_unit shift 2 shift_sq

#check AbsorbingDrazin.StochasticGrammar.transient_drazin
#check AbsorbingDrazin.StochasticGrammar.completion_drazin
#check AbsorbingDrazin.StochasticGrammar.completion_generator_drazin
#check AbsorbingDrazin.generator_solvable_iff
#check SignatureGeometry.observableQuotientEquiv
#check SignatureGeometry.inverse_laws
#check SignatureGeometry.gram_inverse_drazin
#check SignatureGeometry.finite_fredholm_alternative
#check FragmentObservability.historyGram_stein_unique
#check FragmentObservability.historyCrossGram_stein
#check SignatureIdentification.chemical_identifiability_iff
#check SignatureCyclotomic.signature_cyclotomic_laws
#check SpectralOperatorSynthesis.signature_support_iff_all_readouts_zero
#check SpectralOperatorSynthesis.signature_ambient_fourth_power

end InfoGeometry.MassSpectrometry.SignatureOperatorAudit
