/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ExteriorOperatorGeometry
import InfoGeometry.Projective.ExteriorRegressive

/-!
# Faithful operator realization of regressive multiplication

The constructed Hodge equivalence conjugates exterior multiplication to the
regular action of the regressive product. Evaluation on the volume blade
proves this representation faithful. The same identities hold in the full
matrix algebra of the exterior basis.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.GrassmannCayley

open InfoGeometry.Projective.ExteriorRegressive

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (b : Module.Basis (Fin n) K V)

/-- Regular regressive action, explicitly conjugated from exterior multiplication. -/
def regressiveOperator (a : ExteriorAlgebra K V) : Module.End K (ExteriorAlgebra K V) :=
  (hodge b).symm.toLinearMap.comp
    ((Algebra.lmul K (ExteriorAlgebra K V) (hodge b a)).comp (hodge b).toLinearMap)

@[simp] theorem regressiveOperator_apply (a c : ExteriorAlgebra K V) :
    regressiveOperator b a c = regressive b a c := rfl

/-- The full ordered operator composition represents the regressive product. -/
theorem regressiveOperator_mul (a c : ExteriorAlgebra K V) :
    regressiveOperator b (regressive b a c) =
      regressiveOperator b a * regressiveOperator b c := by
  apply LinearMap.ext
  intro d
  simp only [Module.End.mul_apply, regressiveOperator_apply]
  exact regressive_assoc b a c d

/-- The top blade acts as the identity operator. -/
@[simp] theorem regressiveOperator_volume : regressiveOperator b (volume b) = 1 := by
  apply LinearMap.ext
  intro a
  simp only [regressiveOperator_apply, Module.End.one_apply]
  exact volume_regressive b a

@[simp] theorem regressiveOperator_zero :
    regressiveOperator b (0 : ExteriorAlgebra K V) = 0 := by
  apply LinearMap.ext
  intro a
  simp only [regressiveOperator_apply, LinearMap.zero_apply]
  exact zero_regressive b a

theorem regressiveOperator_add (a c : ExteriorAlgebra K V) :
    regressiveOperator b (a + c) = regressiveOperator b a + regressiveOperator b c := by
  apply LinearMap.ext
  intro d
  simp only [regressiveOperator_apply, LinearMap.add_apply]
  exact add_regressive b a c d

theorem regressiveOperator_smul (r : K) (a : ExteriorAlgebra K V) :
    regressiveOperator b (r • a) = r • regressiveOperator b a := by
  apply LinearMap.ext
  intro d
  simp only [regressiveOperator_apply, LinearMap.smul_apply]
  exact smul_regressive b r a d

/-- Evaluation at the volume reconstructs every exterior element. -/
theorem regressiveOperator_injective : Function.Injective (regressiveOperator b) := by
  intro a c h
  have hvol := LinearMap.congr_fun h (volume b)
  simpa only [regressiveOperator_apply, regressive_volume] using hvol

/-- Matrix multiplication represents regressive multiplication without scalarization. -/
theorem matrix_regressiveOperator_mul (a c : ExteriorAlgebra K V) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra
        (regressiveOperator b (regressive b a c)) =
      LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (regressiveOperator b a) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (regressiveOperator b c) := by
  rw [regressiveOperator_mul, map_mul]

/-- The matrix representation is faithful on all, including inhomogeneous, elements. -/
theorem matrix_regressiveOperator_eq_iff (a c : ExteriorAlgebra K V) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (regressiveOperator b a) =
      LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (regressiveOperator b c) ↔ a = c := by
  rw [(LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra).injective.eq_iff]
  exact (regressiveOperator_injective b).eq_iff

/-- Hodge is an explicit intertwiner between the two regular actions. -/
theorem hodge_intertwines_regressive (a : ExteriorAlgebra K V) :
    (hodge b).toLinearMap * regressiveOperator b a =
      Algebra.lmul K (ExteriorAlgebra K V) (hodge b a) * (hodge b).toLinearMap := by
  apply LinearMap.ext
  intro c
  rw [Module.End.mul_apply, Module.End.mul_apply, regressiveOperator_apply]
  change hodge b (regressive b a c) = hodge b a * hodge b c
  exact hodge_regressive b a c

end InfoGeometry.OperatorAlgebra.GrassmannCayley
