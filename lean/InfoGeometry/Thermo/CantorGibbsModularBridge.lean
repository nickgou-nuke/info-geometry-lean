import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Canonical.CantorLocalCl11HopParity
import InfoGeometry.Thermo.FiniteDiagonal
import InfoGeometry.Canonical.AmariBinarySimplexBridge

/-!
# Cantor Gibbs deformation and local modular eigenmodes

This file is an integration layer.  `CantorKMSState` remains the compatible
tracial (β = 0) diagonal reference, while `FiniteDiagonal` supplies the
finite Gibbs weights and real modular shift.  The verified local CAR matrix
units are used only as the off-diagonal eigenmodes of that shift.

No claim about a nontrivial modular group is made for the diagonal algebra:
there the Gibbs state is still pointwise invariant.  The nontrivial modes
below live in the full two-by-two matrix algebra.
-/

noncomputable section

namespace InfoGeometry.Thermo.CantorGibbsModularBridge

open Matrix
open InfoGeometry.Canonical.SplitCliffordCantorFock
open InfoGeometry.Canonical.CantorLocalCl11HopParity
open InfoGeometry.Thermo.FiniteDiagonal
open InfoGeometry.Canonical.AmariBinarySimplexBridge

abbrev LocalMat := M2R

/-- The empty/occupied one-site energies, with the occupied state at ε. -/
def localEnergy (ε : ℝ) : Fin 2 → ℝ := ![0, ε]

/-- The finite one-site Gibbs partition function. -/
noncomputable def localPartition (β ε : ℝ) : ℝ :=
  partition (localEnergy ε) β

/-- The two one-site Gibbs weights. -/
noncomputable def localWeightPlus (β ε : ℝ) : ℝ :=
  gibbsWeight (localEnergy ε) β 0

noncomputable def localWeightMinus (β ε : ℝ) : ℝ :=
  gibbsWeight (localEnergy ε) β 1

theorem localPartition_eq (β ε : ℝ) :
    localPartition β ε = 1 + Real.exp (-β * ε) := by
  unfold localPartition partition localEnergy
  simp [Fin.sum_univ_two]

theorem localWeightPlus_eq (β ε : ℝ) :
    localWeightPlus β ε = 1 / (1 + Real.exp (-β * ε)) := by
  unfold localWeightPlus gibbsWeight
  change Real.exp (-β * localEnergy ε 0) / localPartition β ε = _
  rw [localPartition_eq]
  simp [localEnergy]

theorem localWeightMinus_eq (β ε : ℝ) :
    localWeightMinus β ε = Real.exp (-β * ε) / (1 + Real.exp (-β * ε)) := by
  unfold localWeightMinus gibbsWeight
  change Real.exp (-β * localEnergy ε 1) / localPartition β ε = _
  rw [localPartition_eq]
  simp [localEnergy]

/-! The one-site Gibbs coordinate is exactly the Amari logistic coordinate.
These are finite identities on the same two-state carrier. -/

theorem localWeightPlus_eq_logistic (β ε : ℝ) :
    localWeightPlus β ε = logistic (β * ε) := by
  rw [localWeightPlus_eq]
  unfold logistic
  let x : ℝ := β * ε
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hden : Real.exp x * (1 + Real.exp (-x)) = 1 + Real.exp x := by
    rw [mul_add, mul_one, hprod]
    ring
  have hleft : 1 + Real.exp (-(β * ε)) ≠ 0 := by positivity
  dsimp [x] at hden ⊢
  rw [← hden]
  field_simp [hleft, Real.exp_ne_zero]

theorem localWeightPlus_pos (β ε : ℝ) : 0 < localWeightPlus β ε := by
  unfold localWeightPlus
  exact gibbsWeight_pos (localEnergy ε) β 0

theorem localWeightMinus_pos (β ε : ℝ) : 0 < localWeightMinus β ε := by
  unfold localWeightMinus
  exact gibbsWeight_pos (localEnergy ε) β 1

theorem localWeights_sum_one (β ε : ℝ) :
    localWeightPlus β ε + localWeightMinus β ε = 1 := by
  unfold localWeightPlus localWeightMinus
  simpa using gibbsWeight_sum_one (localEnergy ε) β

theorem localWeightMinus_eq_one_sub_logistic (β ε : ℝ) :
    localWeightMinus β ε = 1 - logistic (β * ε) := by
  rw [← localWeights_sum_one β ε, localWeightPlus_eq_logistic]
  ring

theorem localWeight_variance_eq_fisherExp (β ε : ℝ) :
    localWeightPlus β ε * localWeightMinus β ε = fisherExp (β * ε) := by
  rw [localWeightPlus_eq_logistic,
    localWeightMinus_eq_one_sub_logistic]
  rfl

/-- The one-site Gibbs fluctuation is the squared coherence of the native
finite covariance/Majorana block at the same logistic coordinate. -/
theorem localWeight_variance_eq_covariance_offdiag_sq (β ε : ℝ) :
    localWeightPlus β ε * localWeightMinus β ε =
      (InfoGeometry.Krein.FiniteCovarianceMajoranaBlock.covarianceProjection
        (logistic (β * ε)) 0 1) ^ 2 := by
  rw [localWeight_variance_eq_fisherExp,
    InfoGeometry.Canonical.AmariBinarySimplexBridge.fisherExp_eq_covariance_offdiag_sq]

theorem localWeightPlus_beta_zero (ε : ℝ) :
    localWeightPlus 0 ε = 1 / 2 := by
  rw [localWeightPlus_eq]
  norm_num

theorem localWeightMinus_beta_zero (ε : ℝ) :
    localWeightMinus 0 ε = 1 / 2 := by
  rw [localWeightMinus_eq]
  norm_num

theorem localWeight_transport (β ε : ℝ) :
    localWeightPlus β ε * Real.exp (-β * ε) = localWeightMinus β ε := by
  unfold localWeightPlus localWeightMinus localEnergy
  convert gibbsWeight_transport (localEnergy ε) β 0 1 using 1 <;>
    norm_num [localEnergy]

/-- The real finite-dimensional modular shift at one site. -/
noncomputable def localModularShift (ε t : ℝ) (A : LocalMat) : LocalMat :=
  modularShift (localEnergy ε) t A

theorem localModularShift_plus_fixed (ε t : ℝ) :
    localModularShift ε t localPlusProjection = localPlusProjection := by
  unfold localModularShift
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularShift, localEnergy, localPlusProjection,
      localParityOperator, localVacuumProjection, localOccupiedProjection,
      a_op, aDag_op, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localModularShift_minus_fixed (ε t : ℝ) :
    localModularShift ε t localMinusProjection = localMinusProjection := by
  unfold localModularShift
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularShift, localEnergy, localMinusProjection,
      localParityOperator, localVacuumProjection, localOccupiedProjection,
      a_op, aDag_op, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localModularShift_annihilation_eigenmode (ε t : ℝ) :
    localModularShift ε t a_op = Real.exp (-t * ε) • a_op := by
  unfold localModularShift
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularShift, localEnergy, a_op, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localModularShift_creation_eigenmode (ε t : ℝ) :
    localModularShift ε t aDag_op = Real.exp (t * ε) • aDag_op := by
  unfold localModularShift
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularShift, localEnergy, aDag_op, Matrix.smul_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem localModularShift_zero (ε : ℝ) (A : LocalMat) :
    localModularShift ε 0 A = A := by
  exact modularShift_zero (H := localEnergy ε) A

theorem localModularShift_add (ε s t : ℝ) (A : LocalMat) :
    localModularShift ε (s + t) A =
      localModularShift ε s (localModularShift ε t A) := by
  exact modularShift_add (H := localEnergy ε) s t A

end InfoGeometry.Thermo.CantorGibbsModularBridge
