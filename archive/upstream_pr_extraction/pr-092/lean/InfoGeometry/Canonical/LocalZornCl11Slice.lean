import Mathlib
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

variable {R : Type*} [CommRing R]

/-!
# Local associative Zorn slices

Fixing one vector direction `e` and taking both off-diagonal entries to be
collinear with `e` kills the cross-product terms.  The remaining coordinates
are exactly a 2-by-2 matrix product.  This is a local slice statement, not a
claim that the full Zorn algebra is associative.
-/

def localZornSlice
    (e : ZornVec3 R) (a b u v : R) : ZornVectorMatrix R :=
  ⟨a, u • e, v • e, b⟩

def localZornMatrix
    (a b u v : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![a, u], ![v, b]]

/-!
The four scalar parameters carry the ordinary matrix product.  This is kept
separate from `ZornVectorMatrix.mul`: the latter is the ambient
non-associative product, while this theorem describes only the fixed
one-direction slice.
-/
theorem localZornMatrix_mul
    (a b u v c d x y : R) :
    localZornMatrix a b u v * localZornMatrix c d x y =
      localZornMatrix
        (a * c + u * y)
        (b * d + v * x)
        (a * x + u * d)
        (v * c + b * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localZornMatrix, Matrix.mul_apply] <;> ring

theorem localZornSlice_norm_eq_det
    (e : ZornVec3 R) (he : ZornVec3.dot e e = 1)
    (a b u v : R) :
    ZornVectorMatrix.norm (localZornSlice e a b u v) =
      Matrix.det (localZornMatrix a b u v) := by
  simp [localZornSlice, localZornMatrix, ZornVectorMatrix.norm,
    ZornVec3.dot_smul_left, ZornVec3.dot_smul_right, he,
    Matrix.det_fin_two]
  ring

theorem localZornSlice_mul
    (e : ZornVec3 R)
    (he : ZornVec3.dot e e = 1)
    (hcross : ZornVec3.cross e e = fun _ => 0)
    (a b u v c d x y : R) :
    ZornVectorMatrix.mul
        (localZornSlice e a b u v)
        (localZornSlice e c d x y) =
      localZornSlice e
        (a * c + u * y)
        (b * d + v * x)
        (a * x + u * d)
        (v * c + b * y) := by
  ext i
  · simp [localZornSlice, ZornVectorMatrix.mul,
      ZornVec3.dot_smul_left, ZornVec3.dot_smul_right, he,
      ZornVec3.cross_smul_left, ZornVec3.cross_smul_right, hcross]
    ring
  · fin_cases i <;>
      simp [localZornSlice, ZornVectorMatrix.mul,
        ZornVec3.dot_smul_left, ZornVec3.dot_smul_right, he,
        ZornVec3.cross_smul_left, ZornVec3.cross_smul_right, hcross]
    all_goals ring
  · fin_cases i <;>
      simp [localZornSlice, ZornVectorMatrix.mul,
        ZornVec3.dot_smul_left, ZornVec3.dot_smul_right, he,
        ZornVec3.cross_smul_left, ZornVec3.cross_smul_right, hcross]
    all_goals ring
  · simp [localZornSlice, ZornVectorMatrix.mul,
      ZornVec3.dot_smul_left, ZornVec3.dot_smul_right, he,
      ZornVec3.cross_smul_left, ZornVec3.cross_smul_right, hcross]
    ring

/- The local Zorn multiplication is transported by the parameter matrix. -/
theorem localZornSlice_mul_matrix
    (e : ZornVec3 R)
    (he : ZornVec3.dot e e = 1)
    (hcross : ZornVec3.cross e e = fun _ => 0)
    (a b u v c d x y : R) :
    localZornMatrix
        (a * c + u * y)
        (b * d + v * x)
        (a * x + u * d)
        (v * c + b * y) =
      localZornMatrix a b u v * localZornMatrix c d x y := by
  symm
  exact localZornMatrix_mul a b u v c d x y

/-
The local slice theorem in matrix form.  It is the precise replacement for
the invalid claim that the full Zorn algebra acts associatively on a
projective line.
-/
theorem localZornSlice_mul_to_matrix
    (e : ZornVec3 R)
    (he : ZornVec3.dot e e = 1)
    (hcross : ZornVec3.cross e e = fun _ => 0)
    (a b u v c d x y : R) :
    ZornVectorMatrix.mul
        (localZornSlice e a b u v)
        (localZornSlice e c d x y) =
      localZornSlice e
        ((localZornMatrix a b u v * localZornMatrix c d x y) 0 0)
        ((localZornMatrix a b u v * localZornMatrix c d x y) 1 1)
        ((localZornMatrix a b u v * localZornMatrix c d x y) 0 1)
        ((localZornMatrix a b u v * localZornMatrix c d x y) 1 0) := by
  rw [localZornMatrix_mul]
  exact localZornSlice_mul e he hcross a b u v c d x y

theorem localZorn_basis_direction_norm
    (i : Fin 3) :
    ZornVec3.dot (ZornVec3.basis (R := R) i) (ZornVec3.basis (R := R) i) = 1 := by
  fin_cases i <;> simp [ZornVec3.dot, ZornVec3.basis, Fin.sum_univ_three]

theorem localZorn_basis_direction_cross_self
    (i : Fin 3) :
    ZornVec3.cross (ZornVec3.basis (R := R) i) (ZornVec3.basis (R := R) i) = fun _ => 0 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [ZornVec3.cross, ZornVec3.basis] <;> ring

end InfoGeometry.Canonical
