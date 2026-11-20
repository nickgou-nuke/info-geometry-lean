/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.InternalCubicWeylBasis
import InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AlgebraTower

/-!
# A full real basis from internal cubic clock and shift

The carrier is exactly `RealCubicAdjointWitness.RealCubicOperator`, the full
three-by-three algebra of two-by-two real matrix blocks. The nine actual
clock/shift words form a basis with left operator-valued coefficients.
Mathlib's scalar-tower construction combines it with four real matrix units
to give a native 36-element real basis of the entire algebra.

The internal phase is not replaced by a complex scalar. No commutation with
an arbitrary block entry and no orthonormality of the companion matrix is
assumed. The previous exact cubic differential acts on this same carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealCubicWeylBasis

open scoped BigOperators
open InfoGeometry.Algebra.IsotropicCyclotomicGalois
open InfoGeometry.Algebra.LieCyclotomicBridge
open InfoGeometry.OperatorAlgebra.RealCubicAdjointWitness

private theorem thirdRoot_cyclotomic : cyclo3 thirdRoot = 0 := by
  simpa only [Polynomial.cyclotomic_three, map_add, map_mul, map_pow, Polynomial.aeval_X,
    map_one, pow_two, cyclo3] using thirdRoot_aeval

/-- The coefficient ring is the full two-by-two real matrix algebra. -/
def blockWeylBasis :
    Module.Basis (ZMod 3 × ZMod 3) (Matrix (Fin 2) (Fin 2) ℝ) RealCubicOperator :=
  InternalCubicWeylBasis.weylBasis thirdRoot thirdRoot_cyclotomic

/-- The basis vectors are the existing charge-then-clock words. -/
theorem blockWeylBasis_apply (ab : ZMod 3 × ZMod 3) :
    blockWeylBasis ab = charge ^ ab.1.val * clock ^ ab.2.val := by
  rw [blockWeylBasis, InternalCubicWeylBasis.weylBasis_apply]
  rfl

/-- Coordinates are matrices, with phase factors on their right. -/
theorem blockWeylBasis_repr (X : RealCubicOperator) (ab : ZMod 3 × ZMod 3) :
    blockWeylBasis.repr X ab =
      (1 / 3 : ℝ) • ∑ j : ZMod 3,
        X (j + ab.1) j * thirdRoot ^ (-(ab.2 * j) : ZMod 3).val := rfl

/-- Native scalar-tower basis: four real matrix units times nine cubic words. -/
def realWeylBasis :
    Module.Basis ((Fin 2 × Fin 2) × (ZMod 3 × ZMod 3)) ℝ RealCubicOperator :=
  (Matrix.stdBasis ℝ (Fin 2) (Fin 2)).smulTower blockWeylBasis

/-- Each real basis vector is an actual matrix-unit coefficient times a Weyl word. -/
theorem realWeylBasis_apply (uv : Fin 2 × Fin 2) (ab : ZMod 3 × ZMod 3) :
    realWeylBasis (uv, ab) =
      Matrix.single uv.1 uv.2 (1 : ℝ) • (charge ^ ab.1.val * clock ^ ab.2.val) := by
  rw [realWeylBasis, Module.Basis.smulTower_apply, blockWeylBasis_apply]
  rw [Matrix.stdBasis_eq_single]

private theorem matrix_stdBasis_repr (X : Matrix (Fin 2) (Fin 2) ℝ)
    (uv : Fin 2 × Fin 2) :
    (Matrix.stdBasis ℝ (Fin 2) (Fin 2)).repr X uv = X uv.1 uv.2 := rfl

/-- The real coordinate is the selected entry of the ordered block Fourier coefficient. -/
theorem realWeylBasis_repr (X : RealCubicOperator)
    (uv : Fin 2 × Fin 2) (ab : ZMod 3 × ZMod 3) :
    realWeylBasis.repr X (uv, ab) =
      ((1 / 3 : ℝ) • ∑ j : ZMod 3,
        X (j + ab.1) j * thirdRoot ^ (-(ab.2 * j) : ZMod 3).val) uv.1 uv.2 := by
  rw [realWeylBasis, Module.Basis.smulTower_repr, matrix_stdBasis_repr,
    blockWeylBasis_repr]

/-- Reconstruction holds for every full operator, without a centralizer restriction. -/
theorem realWeylBasis_reconstruction (X : RealCubicOperator) :
    ∑ p : (Fin 2 × Fin 2) × (ZMod 3 × ZMod 3),
      realWeylBasis.repr X p •
        (Matrix.single p.1.1 p.1.2 (1 : ℝ) •
          (charge ^ p.2.1.val * clock ^ p.2.2.val)) = X := by
  calc
    _ = ∑ p, realWeylBasis.repr X p • realWeylBasis p := by
      apply Finset.sum_congr rfl
      rintro ⟨uv, ab⟩ _
      rw [realWeylBasis_apply]
    _ = X := realWeylBasis.sum_repr X

/-- The full carrier has 36 real coordinates, as witnessed by the constructed basis. -/
theorem real_finrank : Module.finrank ℝ RealCubicOperator = 36 := by
  rw [Module.finrank_eq_card_basis realWeylBasis]
  decide

/-- The existing real twisted differential in the constructed 36-coordinate basis. -/
def differentialMatrix :
    Matrix ((Fin 2 × Fin 2) × (ZMod 3 × ZMod 3))
      ((Fin 2 × Fin 2) × (ZMod 3 × ZMod 3)) ℝ :=
  LinearMap.toMatrixAlgEquiv realWeylBasis differential

/-- Exact cubic nilpotency is preserved by the native endomorphism/matrix equivalence. -/
theorem differentialMatrix_cube_zero : differentialMatrix ^ 3 = 0 := by
  change (LinearMap.toMatrixAlgEquiv realWeylBasis differential) ^ 3 = 0
  rw [← map_pow, differential_cube_zero, map_zero]

/-- The coordinate representation preserves the nonzero second iterate as well. -/
theorem differentialMatrix_square_ne_zero : differentialMatrix ^ 2 ≠ 0 := by
  intro h
  apply differential_square_ne_zero
  apply (LinearMap.toMatrixAlgEquiv realWeylBasis).injective
  rw [map_pow, map_zero]
  exact h

end InfoGeometry.OperatorAlgebra.RealCubicWeylBasis
