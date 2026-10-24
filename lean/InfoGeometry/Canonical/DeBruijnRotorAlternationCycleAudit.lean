/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact noncommutative witnesses and API checks; no numerical tolerances. -/

namespace InfoGeometry.Canonical.DeBruijnRotorAlternationCycleAudit

open Matrix InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

/-- The source's integral elementary seed. -/
def matD : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

def matB : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

theorem integral_pair : IsDualSeedPair matD matB := by
  constructor <;> decide

/-- Full matrix equalities, not just selected diagonal entries. -/
theorem mat2Z_deBruijn_rotor_cycle_witness :
    matD * matB ≠ matB * matD ∧
    movingPolePlus (0 : ℤ) 1 matD matB = poleMinus matD matB ∧
    IsIdempotentElem (movingPolePlus (0 : ℤ) 1 matD matB) := by
  dsimp [IsIdempotentElem]
  decide

/-- A nontrivial rational rotation, with both scalar parameters nonzero. -/
theorem rational_moving_pole :
    movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ)
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) !![0, 0; 1, 0] =
        !![9 / 25, -(12 / 25); -(12 / 25), 16 / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [movingPolePlus, peirceBlock, polePlus, exactSupport, poleMinus, coexactSupport,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- A genuine ambient rotor fixes the unused third coordinate. -/
theorem proper_support_rotor :
    phaseRotor (3 / 5 : ℚ) (4 / 5 : ℚ)
      (!![0, 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℚ)
      !![0, 0, 0; 1, 0, 0; 0, 0, 0] =
        !![3 / 5, 4 / 5, 0; -(4 / 5), 3 / 5, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseRotor, completedBlock, peirceBlock, zeroModeSupport, harmonicSupport,
      polePlus, exactSupport, poleMinus, coexactSupport, Matrix.mul_apply, Fin.sum_univ_three]

/-- MP symmetry of the original supports is not enough for a metric rotor. -/
theorem mp_pair_need_not_rotate_to_symmetric_pole :
    let d : Matrix (Fin 2) (Fin 2) ℚ := !![0, 2; 0, 0]
    let b : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1 / 2, 0]
    IsMoorePenroseInverse d b ∧
      (movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) d b).transpose ≠
        movingPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) d b := by
  dsimp
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply])
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    revert h01
    norm_num [movingPolePlus, peirceBlock, polePlus, exactSupport, poleMinus, coexactSupport,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- In characteristic two the double commutator can vanish while the pole moves. -/
theorem characteristic_two_boundary :
    let d : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    let b : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]
    let J := wheelGenerator d b
    let G := phasePolarization d b
    IsDualSeedPair d b ∧
      J * polePlus d b - polePlus d b * J ≠ 0 ∧
      J * (J * G - G * J) - (J * G - G * J) * J = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> decide
  · decide
  · decide

#check phaseRotorUnit
#check phaseRotor_mul
#check phaseRotor_conjugates_plus
#check phaseRotor_conjugates_minus
#check moving_projector_relations
#check moving_poles_sum
#check double_commutator_law
#check no_turning_iff_seeds_vanish
#check poincare_fubini_study_metric_master
#check dualSeedPair_of_mp

end InfoGeometry.Canonical.DeBruijnRotorAlternationCycleAudit
