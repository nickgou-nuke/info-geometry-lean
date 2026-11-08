import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.FiniteSpinDensityRelativeModularBridge

/-!
# Wigner isospin ladder ↔ finite operator-information density bridge

The Wigner raising operator `T₊` is a rank-one `2 × 2` complex amplitude.  Its
normalized left and right Gram densities are exactly the two complementary
spectral projectors of the normalized isospin Cartan `2T₃`.

This gives a concrete nuclear realization of the finite spin-density
intertwining identity

`rho_L * A = A * rho_R`.

Both densities are rank-one projectors and therefore singular.  Consequently
this file does not claim an inverse-based relative modular equivalence for the
pure `T₊` amplitude; such a statement requires support restriction or an
explicit regularization.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearWignerDensityProjectorBridge

open Matrix
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.HestenesSpinDensityXpQuantization
open InfoGeometry.Physics.FiniteSpinDensityRelativeModularBridge

/-- Concrete matrix form of the Wigner raising operator. -/
theorem isospinPlus_eq_rankOne :
    isospinPlus = !![(0 : ℂ), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [isospinPlus, pauli1, pauli2, Complex.I_mul_I] <;> norm_num

/-- The Wigner raising amplitude has unit Gram trace. -/
theorem gramTrace_isospinPlus : gramTrace isospinPlus = 1 := by
  rw [gramTrace_formula, isospinPlus_eq_rankOne]
  norm_num [Complex.normSq]

/-- The left Gram operator of `T₊` is the positive `T₃` projector. -/
theorem gram_isospinPlus : gram isospinPlus = isospinPositiveProjector := by
  rw [isospinPlus_eq_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.HestenesSpinDensityXpQuantization.gram,
      isospinPositiveProjector, Matrix.mul_apply,
      Matrix.conjTranspose, Fin.sum_univ_two]

/-- The right Gram operator of `T₊` is the negative `T₃` projector. -/
theorem rightGram_isospinPlus :
    rightGram isospinPlus = isospinNegativeProjector := by
  rw [isospinPlus_eq_rankOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightGram, isospinNegativeProjector, Matrix.mul_apply,
      Matrix.conjTranspose, Fin.sum_univ_two]

/-- Trace normalization leaves the left rank-one projector unchanged. -/
theorem densityMatrix_isospinPlus :
    densityMatrix isospinPlus = isospinPositiveProjector := by
  unfold densityMatrix
  rw [gramTrace_isospinPlus, gram_isospinPlus]
  simp

/-- Trace normalization leaves the right rank-one projector unchanged. -/
theorem rightDensityMatrix_isospinPlus :
    rightDensityMatrix isospinPlus = isospinNegativeProjector := by
  unfold rightDensityMatrix
  rw [gramTrace_isospinPlus, rightGram_isospinPlus]
  simp

/-- Nuclear charge-exchange intertwining is exactly the general finite
left/right spin-density intertwining law specialized to `T₊`. -/
theorem isospin_projector_intertwining :
    isospinPositiveProjector * isospinPlus =
      isospinPlus * isospinNegativeProjector := by
  have h := spinDensity_intertwines isospinPlus
  rw [densityMatrix_isospinPlus, rightDensityMatrix_isospinPlus] at h
  exact h

/-- The left `T₃` density is singular. -/
theorem isospinPositiveProjector_det_zero :
    isospinPositiveProjector.det = 0 := by
  simp [isospinPositiveProjector, Matrix.det_fin_two]

/-- The right `T₃` density is singular. -/
theorem isospinNegativeProjector_det_zero :
    isospinNegativeProjector.det = 0 := by
  simp [isospinNegativeProjector, Matrix.det_fin_two]

/-- The normalized density pair associated with `T₊` is positive, Hermitian,
trace-one, complementary, and singular. -/
theorem wigner_density_projector_packet :
    densityMatrix isospinPlus = isospinPositiveProjector ∧
      rightDensityMatrix isospinPlus = isospinNegativeProjector ∧
      isospinPositiveProjector + isospinNegativeProjector = 1 ∧
      isospinPositiveProjector * isospinNegativeProjector = 0 ∧
      isospinPositiveProjector.det = 0 ∧
      isospinNegativeProjector.det = 0 :=
  ⟨densityMatrix_isospinPlus,
    rightDensityMatrix_isospinPlus,
    isospinProjector_sum,
    isospinProjector_orthogonal.1,
    isospinPositiveProjector_det_zero,
    isospinNegativeProjector_det_zero⟩

end InfoGeometry.Physics.NuclearWignerDensityProjectorBridge
