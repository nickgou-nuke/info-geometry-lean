/-
The split generator `l` as the algebraic carrier of a Rindler boost.

This is an algebraic bridge only: acceleration selects the real rapidity
parameter, while `lUnit` supplies the hyperbolic generator with square `+1`.
-/

import InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
import InfoGeometry.Thermodynamics.UnruhTemperature

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost

open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Thermodynamics.UnruhTemperature
open InfoGeometry.Canonical.RealTomitaCore

def splitOctonionBoost (η : ℝ) :
    InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ :=
  Real.cosh η •
      (1 : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ) +
    Real.sinh η • lUnit

@[simp] theorem splitOctonionBoost_zero :
    splitOctonionBoost 0 =
      (1 : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ) := by
  simp [splitOctonionBoost]

theorem splitOctonionBoost_add (s t : ℝ) :
    splitOctonionBoost (s + t) =
      zMul (splitOctonionBoost s) (splitOctonionBoost t) := by
  rw [splitOctonionBoost, splitOctonionBoost, splitOctonionBoost,
    Real.cosh_add, Real.sinh_add]
  simp only [zMul_add_left, zMul_add_right, zMul_smul_left, zMul_smul_right,
    zMul_one, one_zMul, l_sq]
  module

/- The boost is diagonal in the scalar chiral/Witt basis. -/
theorem splitOctonionBoost_chiral_decomposition (η : ℝ) :
    splitOctonionBoost η =
      (Real.cosh η + Real.sinh η) •
          chiralNull ⟨0, by decide⟩ 1 +
        (Real.cosh η - Real.sinh η) •
          chiralNull ⟨0, by decide⟩ (-1) := by
  rw [splitOctonionBoost, scalar_chiralNull_plus_idempotent,
    scalar_chiralNull_minus_idempotent]
  module

/- The inverse change of basis recovers the unit and the split generator. -/
theorem one_eq_chiral_sum :
    (1 : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ) =
      chiralNull ⟨0, by decide⟩ 1 + chiralNull ⟨0, by decide⟩ (-1) := by
  rw [scalar_chiralNull_plus_idempotent,
    scalar_chiralNull_minus_idempotent]
  module

theorem lUnit_eq_chiral_difference :
    lUnit =
      chiralNull ⟨0, by decide⟩ 1 - chiralNull ⟨0, by decide⟩ (-1) := by
  rw [scalar_chiralNull_plus_idempotent,
    scalar_chiralNull_minus_idempotent]
  module

/- The same inverse change of basis holds for all four quaternionic
   coordinates, not only for the scalar coordinate. -/
theorem quaternionBasis_eq_chiral_sum (a : Fin 4) :
    quaternionBasis a = chiralNull a 1 + chiralNull a (-1) := by
  rw [chiralNull, chiralNull]
  module

theorem ellBasis_eq_chiral_difference (a : Fin 4) :
    ellBasis a = chiralNull a 1 - chiralNull a (-1) := by
  rw [chiralNull, chiralNull]
  module

/- A mirror representation reverses the hyperbolic generator.  This is the
   exact algebraic interface later used by a modular/CPT representation. -/
theorem linearMirror_chiral_plus_to_minus
    (J : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ →ₗ[ℝ]
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ)
    (hJ_one : J 1 = 1) (hJ_l : J lUnit = -lUnit) :
    J (chiralNull ⟨0, by decide⟩ 1) =
      chiralNull ⟨0, by decide⟩ (-1) := by
  rw [scalar_chiralNull_plus_idempotent,
    scalar_chiralNull_minus_idempotent]
  simp only [map_smul, map_add, hJ_one, hJ_l]
  module

theorem linearMirror_chiral_minus_to_plus
    (J : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ →ₗ[ℝ]
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ)
    (hJ_one : J 1 = 1) (hJ_l : J lUnit = -lUnit) :
    J (chiralNull ⟨0, by decide⟩ (-1)) =
      chiralNull ⟨0, by decide⟩ 1 := by
  rw [scalar_chiralNull_minus_idempotent,
    scalar_chiralNull_plus_idempotent]
  simp only [map_smul, map_sub, hJ_one, hJ_l]
  module

theorem linearMirror_splitOctonionBoost_neg
    (J : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ →ₗ[ℝ]
      InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ)
    (hJ_one : J 1 = 1) (hJ_l : J lUnit = -lUnit) (η : ℝ) :
    J (splitOctonionBoost η) = splitOctonionBoost (-η) := by
  rw [splitOctonionBoost, splitOctonionBoost]
  simp only [map_add, map_smul, hJ_one, hJ_l, Real.cosh_neg,
    Real.sinh_neg, neg_smul]
  module

theorem splitOctonionBoost_chiral_eigenvalue
    (η ε : ℝ) (hε : ε ^ 2 = 1) :
    zMul (splitOctonionBoost η) (chiralNull ⟨0, by decide⟩ ε) =
      (Real.cosh η + ε * Real.sinh η) •
        chiralNull ⟨0, by decide⟩ ε := by
  rw [splitOctonionBoost, zMul_add_left, zMul_smul_left,
    zMul_smul_left, one_zMul, chiralNull_left_ell_eigenvector _ _ hε]
  module

theorem splitOctonionBoost_neg_mul (η : ℝ) :
    zMul (splitOctonionBoost η) (splitOctonionBoost (-η)) =
      (1 : InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ) := by
  rw [← splitOctonionBoost_add, add_neg_cancel, splitOctonionBoost_zero]

theorem splitOctonionBoost_modular_parameter (obs : RindlerObserver) (τmod : ℝ) :
    splitOctonionBoost (rapidity obs (properTime_of_modularTime obs τmod)) =
      splitOctonionBoost (wedgeBoostParameter τmod) := by
  rw [rapidity_properTime_eq_wedgeBoostParameter]

end InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
