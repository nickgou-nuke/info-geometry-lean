/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorLocalCl11HopParity
import InfoGeometry.Thermo.FiniteDiagonal
import InfoGeometry.Canonical.AmariBinarySimplexBridge
import InfoGeometry.Krein.TomitaMatrixAtom
import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

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
open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Algebra.FiniteSpin

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

/-- The zero-energy Gibbs probability is the positive Krein-sector weight at
the thermal polarization `tanh (β ε / 2)`. -/
theorem localWeightPlus_eq_thermalWeightPlus (β ε : ℝ) :
    localWeightPlus β ε =
      InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightPlus
        (Real.tanh (β * ε / 2)) := by
  rw [localWeightPlus_eq_logistic,
    InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_eq_half_add_tanh_half]
  rfl

/-- The complementary Gibbs probability is the negative Krein-sector weight
at the same thermal polarization. -/
theorem localWeightMinus_eq_thermalWeightMinus (β ε : ℝ) :
    localWeightMinus β ε =
      InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightMinus
        (Real.tanh (β * ε / 2)) := by
  rw [localWeightMinus_eq_one_sub_logistic,
    InfoGeometry.Canonical.AmariBinarySimplexBridge.logistic_eq_half_add_tanh_half]
  unfold InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightMinus
  ring

/-- The zero-energy one-site Gibbs weight is the plus-sector probability in
the chiral thermal model at the same rapidity. -/
theorem localWeightPlus_eq_chiralThermalProbabilityPlus (β ε : ℝ) :
    localWeightPlus β ε = chiralThermalProbabilityPlus (β * ε / 2) := by
  rw [localWeightPlus_eq_thermalWeightPlus,
    chiralThermalProbabilityPlus_eq_half_add_tanh]
  rfl

/-- The occupied one-site Gibbs weight is the minus-sector probability in the
chiral thermal model at the same rapidity. -/
theorem localWeightMinus_eq_chiralThermalProbabilityMinus (β ε : ℝ) :
    localWeightMinus β ε = chiralThermalProbabilityMinus (β * ε / 2) := by
  rw [localWeightMinus_eq_thermalWeightMinus,
    chiralThermalProbabilityMinus_eq_half_sub_tanh]
  rfl

/-- The one-site Gibbs variance is the binary Fisher susceptibility at the
thermal polarization coordinate. -/
theorem localWeight_variance_eq_thermal_susceptibility (β ε : ℝ) :
    localWeightPlus β ε * localWeightMinus β ε =
      (1 - Real.tanh (β * ε / 2) ^ 2) / 4 := by
  rw [localWeightPlus_eq_thermalWeightPlus,
    localWeightMinus_eq_thermalWeightMinus]
  unfold InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightPlus
    InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightMinus
  ring

/-- The one-site Gibbs density matrix is the existing two-sector Krein
thermal polarization at contrast `tanh (β ε / 2)`. -/
theorem localGibbsDensity_eq_thermalPolarization (β ε : ℝ) :
    FiniteDiagonal.gibbsDensity (localEnergy ε) β =
      InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization
        (Real.tanh (β * ε / 2)) := by
  ext i j
  fin_cases i <;> fin_cases j
  · convert localWeightPlus_eq_thermalWeightPlus β ε using 1 <;>
      simp [FiniteDiagonal.gibbsDensity, localWeightPlus, localEnergy,
        InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization,
        InfoGeometry.Krein.TomitaMatrixAtom.eps,
        InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightPlus] <;> ring
  · simp [FiniteDiagonal.gibbsDensity,
      InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization,
      InfoGeometry.Krein.TomitaMatrixAtom.eps]
  · simp [FiniteDiagonal.gibbsDensity,
      InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization,
      InfoGeometry.Krein.TomitaMatrixAtom.eps]
  · convert localWeightMinus_eq_thermalWeightMinus β ε using 1 <;>
      simp [FiniteDiagonal.gibbsDensity, localWeightMinus, localEnergy,
        InfoGeometry.Krein.TomitaMatrixAtom.thermalPolarization,
        InfoGeometry.Krein.TomitaMatrixAtom.eps,
        InfoGeometry.Krein.TomitaMatrixAtom.thermalWeightMinus] <;> ring

/-- The negative logarithm of the finite Gibbs density is the log-partition
scalar plus the occupied-sector energy. This is an identity for the existing
diagonal matrix logarithm, not a functional-calculus claim. -/
theorem localSurprisalOp_eq_logPartition_add_occupiedEnergy (β ε : ℝ) :
    -FiniteDiagonal.logDensityOp (localEnergy ε) β =
      Real.log (FiniteDiagonal.partition (localEnergy ε) β) • (1 : Mat2R) +
        (β * ε) • localMinusProjection := by
  rw [localMinusProjection_eq_localOccupiedProjection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteDiagonal.logDensityOp, FiniteDiagonal.logDensityEntry,
      localEnergy, localOccupiedProjection, a_op, aDag_op,
      Matrix.smul_apply, Matrix.add_apply]

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
noncomputable def localModularShift (ε t : ℝ) (A : Mat2R) : Mat2R :=
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

theorem localModularShift_zero (ε : ℝ) (A : Mat2R) :
    localModularShift ε 0 A = A := by
  exact modularShift_zero (H := localEnergy ε) A

theorem localModularShift_add (ε s t : ℝ) (A : Mat2R) :
    localModularShift ε (s + t) A =
      localModularShift ε s (localModularShift ε t A) := by
  exact modularShift_add (H := localEnergy ε) s t A

end InfoGeometry.Thermo.CantorGibbsModularBridge
