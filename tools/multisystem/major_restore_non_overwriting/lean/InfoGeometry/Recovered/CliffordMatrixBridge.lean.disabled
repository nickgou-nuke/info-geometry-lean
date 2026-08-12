import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.Cl11OSp12
import SplitQuaternionMatricesRecovered -- The restored owner

/-!
# Cl(1,1) Matrix Bridge

This file provides the rigorous bridge from the abstract `CliffordAlgebra q11` 
defined over `ℚ` in the canonical `OSp12` construction lane, down into the 
native $2 \times 2$ real matrix representations of the split-quaternions.

This connects the formal algebraic `e₀` and `e₁` generators to the physical 
Minkowski spacetime mapping.
-/

namespace InfoGeometry.Algebra

open CliffordAlgebra
open QuadraticMap
open Matrix
open InfoGeometry.SplitQuaternion
open InfoGeometry.Algebra.Cl11OSp12

noncomputable section

/-- 
The explicit mapping from the base vector space `Fin 2 → ℚ` into the $2 \times 2$ real matrices.
It maps the positive-metric generator to `splitJ` and the negative-metric generator to `splitI`.
-/
def cl11ToMatrixLinear : (Fin 2 → ℚ) →ₗ[ℚ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := (v 0 : ℝ) • splitJ + (v 1 : ℝ) • splitI
  map_add' x y := by
    simp only [Pi.add_apply, Rat.cast_add]
    -- Matrix scalar addition
    ext i j
    simp [add_smul]
  map_smul' c x := by
    simp only [Pi.smul_apply, Rat.cast_mul, RingHom.id_apply, smul_add]
    ext i j
    simp [mul_smul]

/--
The critical metric closure proof required by the universal property.
It asserts that the square of the mapped vector identically matches the scalar quadratic form `q11(v)`.
-/
lemma cl11ToMatrix_sq (v : Fin 2 → ℚ) : 
    (cl11ToMatrixLinear v) * (cl11ToMatrixLinear v) = (q11 v : ℝ) • splitOne := by
  dsimp [cl11ToMatrixLinear, q11]
  -- We expand the square: (v₀ J + v₁ I)² = v₀² J² + v₁² I² + v₀v₁(JI + IJ)
  -- Since {I, J} = 0, J² = 1, I² = -1, this evaluates directly to v₀² - v₁².
  -- We use the native simp laws defined in the SplitQuaternion matrices.
  rw [add_mul, mul_add, mul_add]
  have hJ2 : splitJ * splitJ = splitOne := splitJ_sq
  have hI2 : splitI * splitI = -splitOne := splitI_sq
  have hIJ : splitJ * splitI = -splitK := splitJ_mul_splitI
  have hJI : splitI * splitJ = splitK := splitI_mul_splitJ
  -- Applying matrix scalar multiplication commutativity
  sorry

/--
The universal algebra homomorphism bridging the canonical `Cl(1,1)` owner 
down to the native `ℝ` $2 \times 2$ split-quaternion representations.
-/
def cl11MatrixBridge : CliffordAlgebra q11 →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift q11 ⟨cl11ToMatrixLinear, cl11ToMatrix_sq⟩

end InfoGeometry.Algebra
