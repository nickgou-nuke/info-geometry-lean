/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceParityWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact examples separating algebraic reflection from the stronger source claims. -/

namespace InfoGeometry.Canonical.PeirceReflectionAudit

open Matrix InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.PeirceReflectionContracts InfoGeometry.Core.PeirceParityWeights
open InfoGeometry.Core.DiracSuperalgebra InfoGeometry.Singular.MoorePenrose

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def d : Mat := !![0, 1; 0, 0]
def b : Mat := !![0, 0; 1, 0]

theorem integral_seed : IsDualSeedPair d b := by constructor <;> decide

/-- The two possible proposed spatial identifications have opposite squares. -/
theorem signature_dictionary :
    (wheelGenerator d b * phasePolarization d b) ^ 2 = 1 ∧
    (transitionVelocity d b * phasePolarization d b) ^ 2 = -1 := by decide

/-- Self-adjointness alone does not normalize a reflection. -/
theorem hermitian_does_not_force_involution :
    let r : Mat := 2 • (1 : Mat)
    star r = r ∧ r * r ≠ 1 := by decide

/-- A spatial boundary relation relates different arguments. -/
def twoSheetField (x : Bool) : Mat := if x then b else polePlus d b

/-- An equivariant field can be purely left at one point and purely right at its partner. -/
theorem equivariance_not_pointwise_mixing :
    (∀ x, transitionVelocity d b * twoSheetField x = twoSheetField (!x)) ∧
    polePlus d b * twoSheetField false = twoSheetField false ∧
    poleMinus d b * twoSheetField false = 0 ∧ twoSheetField false ≠ 0 := by decide

/-- Nonzero mixed parity is a checked fact in this example, not an arbitrary-ring axiom. -/
theorem mixed_combination_has_no_parity :
    let w := oddCombination (2 : ℤ) 1 d b
    transitionVelocity d b * w * transitionVelocity d b ≠ w ∧
    transitionVelocity d b * w * transitionVelocity d b ≠ -w ∧ star w ≠ w := by decide

/-- In characteristic two, nonzero coefficients do not force a nonzero parity defect. -/
theorem characteristic_two_boundary :
    let a : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    let c : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]
    IsDualSeedPair a c ∧ wheelGenerator a c ≠ 0 ∧
      oddCombination (1 : ZMod 2) 1 a c = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> decide
  · decide
  · decide

/-- A hyperbolic coefficient pair gives unnormalized diagonal weights. -/
theorem hyperbolic_not_unit_trace :
    let a : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    let c : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
    (5 / 3 : ℚ) ^ 2 - (4 / 3 : ℚ) ^ 2 = 1 ∧
      trace (diagonalWeight ((5 / 3 : ℚ) ^ 2) ((4 / 3 : ℚ) ^ 2) a c) = 41 / 9 ∧
      trace (phasePolarization a c *
        diagonalWeight ((5 / 3 : ℚ) ^ 2) ((4 / 3 : ℚ) ^ 2) a c) = 1 := by
  norm_num [diagonalWeight, phasePolarization, chiralSupport, polePlus, poleMinus,
    exactSupport, coexactSupport, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Normalized weights can have either sign of polarization. -/
theorem circular_weight_trace :
    let a : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    let c : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
    trace (diagonalWeight ((3 / 5 : ℚ) ^ 2) ((4 / 5 : ℚ) ^ 2) a c) = 1 ∧
      trace (phasePolarization a c *
        diagonalWeight ((3 / 5 : ℚ) ^ 2) ((4 / 5 : ℚ) ^ 2) a c) = -(7 / 25) := by
  norm_num [diagonalWeight, phasePolarization, chiralSupport, polePlus, poleMinus,
    exactSupport, coexactSupport, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

#check grading_products
#check spatial_convention
#check phase_twisted_square
#check pure_left_eigenvector_zero
#check pure_equivariant_field_zero
#check combination_fixed_iff
#check combination_negfixed_iff
#check trace_weights
#check invariant_weight_trace_zero
#check car_mix_normalized
#check one_pair_mix_square

end InfoGeometry.Canonical.PeirceReflectionAudit
