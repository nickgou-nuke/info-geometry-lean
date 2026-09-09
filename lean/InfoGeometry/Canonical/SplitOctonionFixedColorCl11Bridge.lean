import Mathlib
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Clifford.Cl11Matrix

/-!
# Fixed-colour `Cl(1,1)` readout in the native Zorn carrier

For a fixed colour, the four native Zorn elements
`E11`, `E22`, `U i`, and `V i` have the multiplication table of the
matrix units of `M₂(ℝ)`.  The ambient Zorn carrier is not associative, so
this file deliberately exposes the result as a linear readout together with
its multiplication theorem.  It does not install an algebra homomorphism
into the full Zorn carrier.
-/

namespace InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Clifford.Cl11Matrix

abbrev Native := ZornMatrix ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-! The matrix-unit readout for one selected colour. -/
def fixedColorReadout (i : Fin 3) (A : Mat2) : Native :=
    { a := A 0 0
      v := A 0 1 • Vec3.basis i
      w := A 1 0 • Vec3.basis i
      b := A 1 1 }

theorem fixedColorReadout_add (i : Fin 3) (A B : Mat2) :
    fixedColorReadout i (A + B) =
      fixedColorReadout i A + fixedColorReadout i B := by
  apply ZornMatrix.ext
  · rfl
  · funext j
    have hV :
        (fixedColorReadout i A + fixedColorReadout i B).v =
          Vec3.add (A 0 1 • Vec3.basis i) (B 0 1 • Vec3.basis i) := rfl
    rw [hV]
    simp only [fixedColorReadout, Matrix.add_apply, Vec3.add, Vec3.smul]
    fin_cases j <;> simp [Vec3.smul] <;> ring
  · funext j
    have hW :
        (fixedColorReadout i A + fixedColorReadout i B).w =
          Vec3.add (A 1 0 • Vec3.basis i) (B 1 0 • Vec3.basis i) := rfl
    rw [hW]
    simp only [fixedColorReadout, Matrix.add_apply, Vec3.add, Vec3.smul]
    fin_cases j <;> simp [Vec3.smul] <;> ring
  · rfl

theorem fixedColorReadout_smul (i : Fin 3) (c : ℝ) (A : Mat2) :
    fixedColorReadout i (c • A) = c • fixedColorReadout i A := by
  apply ZornMatrix.ext
  · rfl
  · funext j
    have hV :
        (c • fixedColorReadout i A).v =
          Vec3.smul c (A 0 1 • Vec3.basis i) := rfl
    rw [hV]
    simp only [fixedColorReadout, ZornMatrix.smul, Vec3.smul,
      Matrix.smul_apply]
    fin_cases j <;> simp [Vec3.smul] <;> ring
  · funext j
    have hW :
        (c • fixedColorReadout i A).w =
          Vec3.smul c (A 1 0 • Vec3.basis i) := rfl
    rw [hW]
    simp only [fixedColorReadout, ZornMatrix.smul, Vec3.smul,
      Matrix.smul_apply]
    fin_cases j <;> simp [Vec3.smul] <;> ring
  · rfl

theorem basis_dot_basis (i : Fin 3) :
    Vec3.dot (Vec3.basis (R := ℝ) i) (Vec3.basis i) = 1 := by
  fin_cases i <;> simp [Vec3.dot, Vec3.basis]

theorem basis_cross_basis (i : Fin 3) :
    Vec3.cross (Vec3.basis (R := ℝ) i) (Vec3.basis i) = fun _ => 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vec3.cross, Vec3.basis]

theorem basis_smul_dot (i : Fin 3) (a b : ℝ) :
    Vec3.dot (a • Vec3.basis (R := ℝ) i)
        (b • Vec3.basis (R := ℝ) i) = a * b := by
  fin_cases i <;>
    simp [Vec3.dot, Vec3.smul, Vec3.basis] <;> ring

theorem basis_smul_cross (i : Fin 3) (a b : ℝ) :
    Vec3.cross (a • Vec3.basis (R := ℝ) i)
        (b • Vec3.basis (R := ℝ) i) = fun _ => 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vec3.cross, Vec3.smul, Vec3.basis]

theorem fixedColor_v_formula (i : Fin 3) (a b c d e f : ℝ) :
    Vec3.sub
        (Vec3.add (Vec3.smul a (b • Vec3.basis i))
          (Vec3.smul d (c • Vec3.basis i)))
        (Vec3.cross (e • Vec3.basis i) (f • Vec3.basis i)) =
      (a * b + d * c) • Vec3.basis i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vec3.sub, Vec3.add, Vec3.smul, Vec3.cross, Vec3.basis] <;>
      ring

theorem fixedColor_w_formula (i : Fin 3) (a b c d e f : ℝ) :
    Vec3.add
        (Vec3.add (Vec3.smul a (b • Vec3.basis i))
          (Vec3.smul d (c • Vec3.basis i)))
        (Vec3.cross (e • Vec3.basis i) (f • Vec3.basis i)) =
      (a * b + d * c) • Vec3.basis i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Vec3.add, Vec3.smul, Vec3.cross, Vec3.basis] <;>
      ring

theorem fixedColorReadout_one (i : Fin 3) :
    fixedColorReadout i (1 : Mat2) = (I : Native) := by
  apply ZornMatrix.ext
  · simp [fixedColorReadout, I, Vec3.smul, Vec3.basis,
      Matrix.one_apply]
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [fixedColorReadout, I, Vec3.smul, Vec3.basis, Matrix.one_apply]
  · funext j
    fin_cases i <;> fin_cases j <;>
      simp [fixedColorReadout, I, Vec3.smul, Vec3.basis, Matrix.one_apply]
  · simp [fixedColorReadout, I, Vec3.smul, Vec3.basis,
      Matrix.one_apply]

theorem fixedColorReadout_mul (i : Fin 3) (A B : Mat2) :
    fixedColorReadout i (A * B) =
      fixedColorReadout i A * fixedColorReadout i B := by
  apply ZornMatrix.ext
  · fin_cases i <;>
    simp only [fixedColorReadout, ZornMatrix.mul_eq_mul, ZornMatrix.mul,
      Vec3.add, Vec3.sub,
      Vec3.smul, Matrix.mul_apply, Fin.sum_univ_two, basis_smul_dot]
    <;> ring
  · funext j
    change (A * B) 0 1 * Vec3.basis i j =
      (Vec3.sub
        (Vec3.add (Vec3.smul (A 0 0) (B 0 1 • Vec3.basis i))
          (Vec3.smul (B 1 1) (A 0 1 • Vec3.basis i)))
        (Vec3.cross (A 1 0 • Vec3.basis i) (B 1 0 • Vec3.basis i))) j
    rw [fixedColor_v_formula i (A 0 0) (B 0 1) (A 0 1)
      (B 1 1) (A 1 0) (B 1 0)]
    simp [Vec3.basis, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · funext j
    change (A * B) 1 0 * Vec3.basis i j =
      (Vec3.add
        (Vec3.add (Vec3.smul (B 0 0) (A 1 0 • Vec3.basis i))
          (Vec3.smul (A 1 1) (B 1 0 • Vec3.basis i)))
        (Vec3.cross (A 0 1 • Vec3.basis i) (B 0 1 • Vec3.basis i))) j
    rw [fixedColor_w_formula i (B 0 0) (A 1 0) (B 1 0)
      (A 1 1) (A 0 1) (B 0 1)]
    simp [Vec3.basis, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp only [fixedColorReadout, ZornMatrix.mul_eq_mul, ZornMatrix.mul,
      Vec3.add, Vec3.sub,
      Vec3.smul, Matrix.mul_apply, Fin.sum_univ_two, basis_smul_dot]

theorem fixedColorReadout_injective (i : Fin 3) :
    Function.Injective (fixedColorReadout i) := by
  intro A B h
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c
  · exact congrArg ZornMatrix.a h
  · simpa [fixedColorReadout, Vec3.smul, Vec3.basis] using
      congrArg (fun X => X.v i) h
  · simpa [fixedColorReadout, Vec3.smul, Vec3.basis] using
      congrArg (fun X => X.w i) h
  · exact congrArg ZornMatrix.b h

/-! The native fixed-colour readout of the abstract `Cl(1,1)` algebra. -/
noncomputable def cl11ToFixedColor (i : Fin 3) :
    CliffordAlgebra q11 → Native :=
  fun x => fixedColorReadout i (cl11EquivMat x)

theorem cl11ToFixedColor_one (i : Fin 3) :
    cl11ToFixedColor i (1 : CliffordAlgebra q11) = (I : Native) := by
  simp [cl11ToFixedColor, fixedColorReadout_one]

theorem cl11ToFixedColor_mul (i : Fin 3)
    (x y : CliffordAlgebra q11) :
    cl11ToFixedColor i (x * y) =
      cl11ToFixedColor i x * cl11ToFixedColor i y := by
  change fixedColorReadout i (cl11EquivMat (x * y)) =
    fixedColorReadout i (cl11EquivMat x) *
      fixedColorReadout i (cl11EquivMat y)
  rw [map_mul]
  exact fixedColorReadout_mul i (cl11EquivMat x) (cl11EquivMat y)

theorem cl11ToFixedColor_injective (i : Fin 3) :
    Function.Injective (cl11ToFixedColor i) := by
  exact (fixedColorReadout_injective i).comp cl11EquivMat.injective

end InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge
