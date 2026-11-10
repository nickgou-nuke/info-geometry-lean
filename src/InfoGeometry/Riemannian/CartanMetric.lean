/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

namespace InfoGeometry.Riemannian

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Over any non-commutative ring `[Ring B]`, the unnormalized symmetrized Cartan pairing
`(x, y) ↦ x * y + y * x` is symmetric and reduces on the diagonal to `2 * (x * x)`. -/
theorem ring_cartan_symmetrized_pairing
    {B : Type*} [Ring B] (x y : B) :
    (x * y + y * x = y * x + x * y) ∧ (x * x + x * x = 2 * (x * x)) :=
  ⟨add_comm (x * y) (y * x), (two_mul (x * x)).symm⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Дефиниране на следата на произволен паравектор като неговата скаларна част (grade 0).
    Имплементирано строго конструктивно чрез каноничния изоморфизъм с ExteriorAlgebra. -/
def hTrace_cl : CliffordAlgebra Q →ₗ[R] R :=
  (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap.comp (CliffordAlgebra.equivExterior Q).toLinearMap

def hTrace (X : evenOdd Q 0) : R :=
  hTrace_cl Q X.val

theorem hTrace_add (A B : evenOdd Q 0) : hTrace Q (A + B) = hTrace Q A + hTrace Q B := by
  change hTrace_cl Q (A.val + B.val) = hTrace_cl Q A.val + hTrace_cl Q B.val
  exact map_add (hTrace_cl Q) A.val B.val

theorem hTrace_smul (c : R) (A : evenOdd Q 0) : hTrace Q (c • A) = c * hTrace Q A := by
  change hTrace_cl Q (c • A.val) = c * hTrace_cl Q A.val
  exact LinearMap.map_smul (hTrace_cl Q) c A.val

theorem hTrace_zero : hTrace Q 0 = 0 := by
  change hTrace_cl Q 0 = 0
  exact map_zero (hTrace_cl Q)

theorem hTrace_one : hTrace Q 1 = 1 := by
  have h1 : (1 : evenOdd Q 0).val = 1 := rfl
  change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap (CliffordAlgebra.equivExterior Q 1) = 1
  simp

end InfoGeometry.Riemannian
