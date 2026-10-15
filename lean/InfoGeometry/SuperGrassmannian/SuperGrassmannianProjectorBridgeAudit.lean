/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge

/-!
# Super-Grassmannian Projector Bridge Audit

Kernel audit verifying:
1. `paraProjectorMinus_idempotent`
2. `paraProjectorPlus_idempotent`
3. `paraProjectors_sum_id`
4. `covectorVacuumSheet_eq_range_projectorMinus`
5. `primalSheet_eq_range_projectorPlus`
6. `covector_vacuum_sheet_is_isotropic`
7. `primal_sheet_is_isotropic`
8. `cl_nn_vacuum_sheet_quadratic_null`
-/

namespace InfoGeometry.SuperGrassmannian.Audit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v)
variable (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h_anti : ∀ u v, g (K u) (K v) = - g u v)

#print axioms paraProjectorMinus_idempotent
#print axioms paraProjectorPlus_idempotent
#print axioms paraProjectors_sum_id
#print axioms covectorVacuumSheet_eq_range_projectorMinus
#print axioms primalSheet_eq_range_projectorPlus
#print axioms covector_vacuum_sheet_is_isotropic
#print axioms primal_sheet_is_isotropic
#print axioms cl_nn_vacuum_sheet_quadratic_null

end InfoGeometry.SuperGrassmannian.Audit
