/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornGramDissipation
import InfoGeometry.Thermo.GenericEntropyExtension

/-!
# Entropy-coordinate systems from the two actual Zorn Gram operators

The positive coefficient duality turns the ambient and quaternion-projected
associator forms into genuine mobilities. A concrete skew, invertible rotation
on the eight-dimensional Zorn vector space supplies the reversible operator.
The existing entropy extension then constructs both systems on `Z × ℝ`.

Their entropy rates vanish on different, explicitly characterized sets of
energy covectors. A quaternion-unit covector has positive ambient production
and zero projected production; `E11` has positive projected production.
These are pointwise linear systems. No Jacobi identity, trajectory existence,
thermodynamic interpretation of the reference pairing, or uniqueness is inferred.
-/

noncomputable section

namespace InfoGeometry.Thermo.ZornEntropyExtension

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornPinorReconstruction
open InfoGeometry.Algebra.ZornCARAdjoint
open InfoGeometry.Algebra.ZornAssociatorGram
open InfoGeometry.Algebra.ZornQuaternionProjectedGram
open InfoGeometry.Algebra.ZornGramDissipation
open InfoGeometry.Canonical.GunaydinGursey
open GenericMetriplecticFlow

/-- A real orthogonal complex structure on the full Zorn vector space. -/
def coefficientRotation : Z →ₗ[ℝ] Z where
  toFun X := ⟨-X.b, -X.w, X.v, X.a⟩
  map_add' X Y := by
    ext i <;> simp [ZornVectorMatrix.add] <;> ring
  map_smul' r X := by
    ext i <;> simp [ZornVectorMatrix.smul]

@[simp] theorem coefficientRotation_sq (X : Z) :
    coefficientRotation (coefficientRotation X) = -X := by
  ext i <;> simp [coefficientRotation, ZornVectorMatrix.neg]

theorem coefficientRotation_injective : Function.Injective coefficientRotation := by
  intro X Y h
  have hh := congrArg coefficientRotation h
  simpa only [coefficientRotation_sq, neg_inj] using hh

theorem coefficientRotation_skew (X Y : Z) :
    coefficientPairing X (coefficientRotation Y) =
      -coefficientPairing Y (coefficientRotation X) := by
  simp [coefficientRotation, coefficientPairing, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- A constructed injective reversible operator with the correct covector variance. -/
def canonicalReversible : Covector Z →ₗ[ℝ] Z :=
  coefficientRotation.comp coefficientDuality.symm.toLinearMap

theorem canonicalReversible_pairing (φ ψ : Covector Z) :
    φ (canonicalReversible ψ) =
      coefficientPairing (coefficientDuality.symm φ)
        (coefficientRotation (coefficientDuality.symm ψ)) :=
  (coefficientDuality_symm_pairing φ _).symm

theorem canonicalReversible_skew (φ ψ : Covector Z) :
    φ (canonicalReversible ψ) = -ψ (canonicalReversible φ) := by
  rw [canonicalReversible_pairing, canonicalReversible_pairing]
  exact coefficientRotation_skew _ _

theorem canonicalReversible_injective : Function.Injective canonicalReversible :=
  coefficientRotation_injective.comp coefficientDuality.symm.injective

/-- Entropy extension using all ambient associator probes. -/
def ambientSystem (h : Covector Z) (T : ℝ) (hT : 0 < T) : System (Z × ℝ) :=
  GenericEntropyExtension.system canonicalReversible ambientDissipation h T hT
    canonicalReversible_skew ambientDissipation_symmetric ambientDissipation_nonneg

/-- Entropy extension using the quaternion-projected associator probes. -/
def quaternionSystem (h : Covector Z) (T : ℝ) (hT : 0 < T) : System (Z × ℝ) :=
  GenericEntropyExtension.system canonicalReversible quaternionDissipation h T hT
    canonicalReversible_skew quaternionDissipation_symmetric quaternionDissipation_nonneg

/-- The concrete extension acquires exactly the nonzero entropy line as kernel. -/
theorem quaternionSystem_reversible_kernel (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    LinearMap.ker (quaternionSystem h T hT).L =
      Submodule.span ℝ {(GenericEntropyExtension.entropyCovector : Covector (Z × ℝ))} :=
  GenericEntropyExtension.reversible_kernel canonicalReversible canonicalReversible_injective

theorem ambientSystem_entropy_rate (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    (ambientSystem h T hT).dS (ambientSystem h T hT).flow =
      T⁻¹ ^ 3 * associatorGram (coefficientDuality.symm h) (coefficientDuality.symm h) := by
  unfold ambientSystem
  rw [GenericEntropyExtension.system_entropy_rate]
  change T⁻¹ ^ 3 * h (gramCovectorOperator associatorGram h) = _
  rw [gramCovectorOperator_eval]

theorem quaternionSystem_entropy_rate (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    (quaternionSystem h T hT).dS (quaternionSystem h T hT).flow =
      T⁻¹ ^ 3 * projectedAssociatorGram
        (coefficientDuality.symm h) (coefficientDuality.symm h) := by
  unfold quaternionSystem
  rw [GenericEntropyExtension.system_entropy_rate]
  change T⁻¹ ^ 3 * h (gramCovectorOperator projectedAssociatorGram h) = _
  rw [gramCovectorOperator_eval]

/-- Zero production for the ambient mobility is exactly the scalar-nucleus condition. -/
theorem ambientSystem_entropy_rate_eq_zero_iff (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    (ambientSystem h T hT).dS (ambientSystem h T hT).flow = 0 ↔
      ∃ r : ℝ, coefficientDuality.symm h = r • (ZornVectorMatrix.one : Z) := by
  rw [ambientSystem_entropy_rate]
  have hc : T⁻¹ ^ 3 ≠ 0 := pow_ne_zero 3 (inv_ne_zero (ne_of_gt hT))
  constructor
  · intro hz
    exact (associatorGram_zero_iff_scalar _).mp ((mul_eq_zero.mp hz).resolve_left hc)
  · intro hh
    rw [(associatorGram_zero_iff_scalar _).mpr hh, mul_zero]

/-- Zero production for the projected mobility is exactly the quaternion-range condition. -/
theorem quaternionSystem_entropy_rate_eq_zero_iff (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    (quaternionSystem h T hT).dS (quaternionSystem h T hT).flow = 0 ↔
      coefficientDuality.symm h ∈ LinearMap.range quaternionEmbedding := by
  rw [quaternionSystem_entropy_rate]
  have hc : T⁻¹ ^ 3 ≠ 0 := pow_ne_zero 3 (inv_ne_zero (ne_of_gt hT))
  constructor
  · intro hz
    exact (projectedAssociatorGram_zero_iff _).mp ((mul_eq_zero.mp hz).resolve_left hc)
  · intro hh
    rw [(projectedAssociatorGram_zero_iff _).mpr hh, mul_zero]

/-- Strict production is the complement of the entire quaternion register. -/
theorem quaternionSystem_entropy_rate_pos_iff (h : Covector Z) (T : ℝ) (hT : 0 < T) :
    0 < (quaternionSystem h T hT).dS (quaternionSystem h T hT).flow ↔
      coefficientDuality.symm h ∉ LinearMap.range quaternionEmbedding := by
  constructor
  · intro hpos hmem
    have hz := (quaternionSystem_entropy_rate_eq_zero_iff h T hT).mpr hmem
    exact (ne_of_gt hpos) hz
  · intro hmem
    rw [quaternionSystem_entropy_rate]
    exact mul_pos (pow_pos (inv_pos.mpr hT) 3)
      (projectedAssociatorGram_pos_of_not_quaternion hmem)

/-- A fully constructed system has strictly positive entropy production. -/
theorem quaternionSystem_E11_entropy_pos (T : ℝ) (hT : 0 < T) :
    0 < (quaternionSystem (coefficientDuality ZornVectorMatrix.E11) T hT).dS
      (quaternionSystem (coefficientDuality ZornVectorMatrix.E11) T hT).flow := by
  rw [quaternionSystem_entropy_rate, LinearEquiv.symm_apply_apply]
  exact mul_pos (pow_pos (inv_pos.mpr hT) 3) projectedAssociatorGram_E11_pos

/-- The two systems give genuinely different production on the same energy covector. -/
theorem quaternion_i_entropy_contrast (T : ℝ) (hT : 0 < T) :
    (quaternionSystem
      (coefficientDuality (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))) T hT).dS
      (quaternionSystem
        (coefficientDuality (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))) T hT).flow = 0 ∧
    0 < (ambientSystem
      (coefficientDuality (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))) T hT).dS
      (ambientSystem
        (coefficientDuality (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))) T hT).flow := by
  constructor
  · rw [quaternionSystem_entropy_rate, LinearEquiv.symm_apply_apply,
      projectedAssociatorGram_quaternion, mul_zero]
  · rw [ambientSystem_entropy_rate, LinearEquiv.symm_apply_apply]
    exact mul_pos (pow_pos (inv_pos.mpr hT) 3) associatorGram_quaternion_i_pos

end InfoGeometry.Thermo.ZornEntropyExtension

end
