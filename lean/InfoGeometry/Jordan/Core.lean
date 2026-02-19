import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# Jordan Algebra Core

Minimal linear Jordan-algebra interface used by InfoGeometry.
-/

namespace InfoGeometry.Jordan

/-- A real linear Jordan algebra structure on `V`. -/
class JordanAlgebra (V : Type _) [AddCommGroup V] [Module ℝ V] where
  jordanProd : V → V → V
  add_left : ∀ x y z, jordanProd (x + y) z = jordanProd x z + jordanProd y z
  smul_left : ∀ (a : ℝ) x y, jordanProd (a • x) y = a • jordanProd x y
  comm : ∀ x y, jordanProd x y = jordanProd y x
  jordan_identity :
    ∀ x y,
      jordanProd (jordanProd x x) (jordanProd x y) =
        jordanProd x (jordanProd (jordanProd x x) y)

infixl:70 " ⊙ " => JordanAlgebra.jordanProd

section

variable {V : Type _} [AddCommGroup V] [Module ℝ V] [JordanAlgebra V]

@[simp]
lemma jordanProd_comm (x y : V) : x ⊙ y = y ⊙ x :=
  JordanAlgebra.comm x y

@[simp]
lemma jordanProd_add_left (x y z : V) :
    (x + y) ⊙ z = x ⊙ z + y ⊙ z :=
  JordanAlgebra.add_left x y z

@[simp]
lemma jordanProd_smul_left (a : ℝ) (x y : V) :
    (a • x) ⊙ y = a • (x ⊙ y) :=
  JordanAlgebra.smul_left a x y

@[simp]
lemma jordanProd_add_right (x y z : V) :
    x ⊙ (y + z) = x ⊙ y + x ⊙ z := by
  rw [jordanProd_comm, JordanAlgebra.add_left y z x, jordanProd_comm y x, jordanProd_comm z x]

@[simp]
lemma jordanProd_smul_right (a : ℝ) (x y : V) :
    x ⊙ (a • y) = a • (x ⊙ y) := by
  rw [jordanProd_comm, JordanAlgebra.smul_left a y x, jordanProd_comm y x]

lemma jordanProd_identity (x y : V) :
    (x ⊙ x) ⊙ (x ⊙ y) = x ⊙ ((x ⊙ x) ⊙ y) :=
  JordanAlgebra.jordan_identity x y

end

end InfoGeometry.Jordan
