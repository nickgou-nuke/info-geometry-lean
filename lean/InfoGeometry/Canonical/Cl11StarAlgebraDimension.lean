/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11StarAlgebraColimit
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Dimension and noncommutativity of the real full matrix tensor limit

Faithful inclusions of full matrix algebras with unbounded dimensions make
the existing real algebraic limit infinite-dimensional. The existing two
stage-one gamma matrices give an explicit pair of noncommuting elements in
that same carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11StarAlgebraDimension

open InfoGeometry.Canonical.Cl11StarAlgebraColimit
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The dimension of a full real tensor stage is the square of its matrix size. -/
theorem stage_finrank (n : ℕ) :
    Module.finrank ℝ (Stage n) = 2 ^ n * 2 ^ n := by
  change Module.finrank ℝ (Matrix (TowerMatrix.Idx n) (TowerMatrix.Idx n) ℝ) = _
  simp only [Module.finrank_matrix, TowerMatrix.idx_card_pow_two,
    Module.finrank_self, mul_one]

/-- The existing algebraic tensor limit is not a finite-dimensional real algebra. -/
theorem not_finiteDimensional : ¬ FiniteDimensional ℝ Limit := by
  intro h
  letI : FiniteDimensional ℝ Limit := h
  let d := Module.finrank ℝ Limit
  have hle : Module.finrank ℝ (Stage d) ≤ d :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (ofStageStarAlgHom d).toAlgHom.toLinearMap)
      (ofStageStarAlgHom_injective d)
  rw [stage_finrank] at hle
  exact (d.lt_two_pow_self.trans_le (Nat.le_mul_self (2 ^ d))).not_ge hle

/-- The existing stage-one real gamma matrices do not commute. -/
theorem stage_one_generators_mul_ne :
    gamma_0 * gamma_1 ≠ gamma_1 * gamma_0 := by
  intro h
  have hentry := congrArg
    (fun A : Stage 1 => A ((0 : Fin 1), (0 : Fin 2)) ((0 : Fin 1), (0 : Fin 2))) h
  simp only [Matrix.mul_apply] at hentry
  norm_num [gamma_0, gamma_1, gamma_0_base, gamma_1_base,
    TowerMatrix.kronPow, TowerMatrix.Idx, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_succ] at hentry

/-- Two actual elements of the algebraic limit have unequal ordered products. -/
theorem exists_noncommuting : ∃ a b : Limit, a * b ≠ b * a := by
  refine ⟨ofStageStarAlgHom 1 gamma_0, ofStageStarAlgHom 1 gamma_1, ?_⟩
  intro h
  apply stage_one_generators_mul_ne
  apply ofStageStarAlgHom_injective 1
  simpa only [map_mul] using h

end InfoGeometry.Canonical.Cl11StarAlgebraDimension
