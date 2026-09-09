/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

/-!
# Arnold--Kohno / para-Kähler connection interface

This owner is deliberately an interface between the repository's native
Arnold--Cohen relations and its finite para-Kähler datum.  It does not
identify an arbitrary KZ connection with a metric, nor does it assert a
general configuration-space theorem without an indexed residue carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

open InfoGeometry.Canonical.ArnoldCohenBCFWBridge
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

/-- A finite commutator connection is flat when its coefficient values
commute.  The exterior/formal differential part is kept separate from this
algebraic curvature statement. -/
structure CommutatorConnection (A V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] where
  coefficient : V → A

/-- The curvature of a pair of coefficients is their commutator. -/
def commutatorCurvature {A V : Type*} [Ring A] [AddCommGroup V]
    [Module A V] (C : CommutatorConnection A V) (u v : V) : A :=
  C.coefficient u * C.coefficient v -
    C.coefficient v * C.coefficient u

theorem commutatorCurvature_eq_zero_of_commuting
    {A V : Type*} [Ring A] [AddCommGroup V] [Module A V]
    (C : CommutatorConnection A V)
    (hcomm : ∀ u v, C.coefficient u * C.coefficient v =
      C.coefficient v * C.coefficient u) (u v : V) :
    commutatorCurvature C u v = 0 := by
  simp [commutatorCurvature, hcomm u v]

/-- Scalar coefficients give a canonical flat commutator connection. -/
theorem scalar_commutator_curvature_zero
    {R A V : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup V] [Module R V]
    (f : V → R) (u v : V) :
    (algebraMap R A (f u)) * algebraMap R A (f v) -
      algebraMap R A (f v) * algebraMap R A (f u) = 0 := by
  exact sub_eq_zero.mpr (Algebra.commutes (f u) (algebraMap R A (f v)))


/-! The three-channel calculation works in a native Lie algebra of residues,
independently of the exterior algebra of forms. It proves the quadratic
curvature cancellation only; differential closure requires a separate theorem. -/

open scoped TensorProduct

section Triangle

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]

/-- The three commutator-weighted exterior channels of a triangle. -/
def triangleCurvature (x y z : L) (a b c : ExteriorAlgebra R M) :
    L ⊗[R] ExteriorAlgebra R M :=
  ⁅x, y⁆ ⊗ₜ[R] (a * b) + ⁅y, z⁆ ⊗ₜ[R] (b * c) + ⁅z, x⁆ ⊗ₜ[R] (c * a)

/-- One infinitesimal braid relation identifies the third cyclic bracket. -/
theorem kohno_third_coefficient (x y z : L) (h : ⁅x, z + y⁆ = 0) :
    ⁅z, x⁆ = ⁅x, y⁆ := by
  have hxy : ⁅x, z⁆ = -⁅x, y⁆ :=
    eq_neg_of_add_eq_zero_left (by simpa only [lie_add] using h)
  rw [← lie_skew z x, hxy, neg_neg]

/-- The other infinitesimal braid relation identifies the second cyclic bracket. -/
theorem kohno_second_coefficient (x y z : L) (h : ⁅y, x + z⁆ = 0) :
    ⁅y, z⁆ = ⁅x, y⁆ := by
  have hyz : ⁅y, z⁆ = -⁅y, x⁆ :=
    eq_neg_of_add_eq_zero_right (by simpa only [lie_add] using h)
  rw [hyz, lie_skew x y]

/-- Kohno's relations factor the tensor-valued curvature through the Arnold term. -/
theorem triangleCurvature_factorizes (x y z : L) (a b c : ExteriorAlgebra R M)
    (hx : ⁅x, z + y⁆ = 0) (hy : ⁅y, x + z⁆ = 0) :
    triangleCurvature x y z a b c =
      ⁅x, y⁆ ⊗ₜ[R] (a * b + b * c + c * a) := by
  rw [triangleCurvature, kohno_second_coefficient x y z hy,
    kohno_third_coefficient x y z hx]
  simp only [TensorProduct.tmul_add]

/-- The Arnold relation cancels the quadratic curvature after Kohno reduction. -/
theorem arnold_kohno_triangle_flat (x y z : L) (a b c : ExteriorAlgebra R M)
    (hArnold : a * b + b * c + c * a = 0)
    (hx : ⁅x, z + y⁆ = 0) (hy : ⁅y, x + z⁆ = 0) :
    triangleCurvature x y z a b c = 0 := by
  rw [triangleCurvature_factorizes x y z a b c hx hy, hArnold]
  simp only [TensorProduct.tmul_zero]

end Triangle

end InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
