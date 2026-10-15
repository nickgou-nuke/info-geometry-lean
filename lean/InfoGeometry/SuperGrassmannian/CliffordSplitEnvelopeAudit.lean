/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.CliffordSplitEnvelope

/-!
# Clifford Split Envelope Audit

Kernel audit verifying:
1. `cross_symmetry`
2. `cl_nn_quadratic_form_split`
3. `primal_vacuum_pairing_nondegenerate`
-/

namespace InfoGeometry.SuperGrassmannian.Audit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v)
variable (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
variable (h_symm : ∀ u v, g u v = g v u)
variable (hg : ∀ u v, g (K u) (K v) = - g u v)

#print axioms cross_symmetry
#print axioms cl_nn_quadratic_form_split
#print axioms primal_vacuum_pairing_nondegenerate

end InfoGeometry.SuperGrassmannian.Audit
