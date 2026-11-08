import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

namespace ThreeDMirrorSymmetry

theorem complex_add_comm (a b : ℂ) : a + b = b + a := add_comm a b

theorem complex_mul_comm (a b : ℂ) : a * b = b * a := mul_comm a b

theorem matrix_add_comm {n : Type*} (A B : Matrix n n ℂ) : A + B = B + A := add_comm A B

end ThreeDMirrorSymmetry