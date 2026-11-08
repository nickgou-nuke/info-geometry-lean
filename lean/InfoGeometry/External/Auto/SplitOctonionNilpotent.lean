import InfoGeometry.External.Auto.OctonionMatrixEncodings
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-octonion nilpotent zero mode

This file records a concrete nonzero Zorn element whose square and split norm
are zero.
-/

noncomputable section

namespace SplitOctonionNilpotent

abbrev Vec3 := OctonionMatrixEncodings.Vec3
abbrev ZornMatrix := OctonionMatrixEncodings.Zorn

/-- Zero Zorn vector-matrix. -/
def ZornMatrix.zero : ZornMatrix where
  a := 0
  u := fun _ => 0
  v := fun _ => 0
  b := 0

/-- Zorn multiplication. -/
def zornMul : ZornMatrix → ZornMatrix → ZornMatrix := OctonionMatrixEncodings.zornMul

/-- Split-octonion quadratic norm in the integer Zorn model. -/
def zornNorm (A : ZornMatrix) : ℤ :=
  A.a * A.b - OctonionMatrixEncodings.dot3 A.u A.v

/-- A nonzero upper-vector Zorn element. -/
def Z_mode : ZornMatrix := OctonionMatrixEncodings.Zy

/-- The Zorn zero mode is nonzero. -/
theorem Z_mode_nonzero : Z_mode ≠ ZornMatrix.zero := by
  intro h
  have hu := congrArg (fun W : ZornMatrix => W.u 0) h
  simp [Z_mode, ZornMatrix.zero, OctonionMatrixEncodings.Zy,
    OctonionMatrixEncodings.basis3] at hu

/-- The Zorn zero mode squares to zero. -/
theorem Z_mode_nilpotent : zornMul Z_mode Z_mode = ZornMatrix.zero := by
  apply OctonionMatrixEncodings.zorn_ext
  · simp [zornMul, Z_mode, ZornMatrix.zero, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.Zy, OctonionMatrixEncodings.basis3,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3]
  · funext i
    fin_cases i <;> simp [zornMul, Z_mode, ZornMatrix.zero, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.Zy, OctonionMatrixEncodings.basis3,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3]
  · funext i
    fin_cases i <;> simp [zornMul, Z_mode, ZornMatrix.zero, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.Zy, OctonionMatrixEncodings.basis3,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3]
  · simp [zornMul, Z_mode, ZornMatrix.zero, OctonionMatrixEncodings.zornMul,
      OctonionMatrixEncodings.Zy, OctonionMatrixEncodings.basis3,
      OctonionMatrixEncodings.dot3, OctonionMatrixEncodings.cross3]

/-- The same zero mode lies on the split norm-null cone. -/
theorem Z_mode_null : zornNorm Z_mode = 0 := by
  simp [zornNorm, Z_mode, OctonionMatrixEncodings.Zy, OctonionMatrixEncodings.dot3]

/-- The diagonal Zorn element is isotropic but idempotent.  Thus the null
condition for the split composition norm is not the same as the equation
`x * x = 0`; a null element need not be square-zero. -/
theorem Zx_null_idempotent :
    zornNorm OctonionMatrixEncodings.Zx = 0 ∧
      zornMul OctonionMatrixEncodings.Zx OctonionMatrixEncodings.Zx =
        OctonionMatrixEncodings.Zx := by
  constructor
  · simp [zornNorm, OctonionMatrixEncodings.Zx,
      OctonionMatrixEncodings.dot3]
  · apply OctonionMatrixEncodings.zorn_ext
    · simp [zornMul, OctonionMatrixEncodings.zornMul,
        OctonionMatrixEncodings.Zx, OctonionMatrixEncodings.dot3]
    · funext i
      fin_cases i <;> simp [zornMul, OctonionMatrixEncodings.zornMul,
        OctonionMatrixEncodings.Zx, OctonionMatrixEncodings.dot3,
        OctonionMatrixEncodings.cross3]
    · funext i
      fin_cases i <;> simp [zornMul, OctonionMatrixEncodings.zornMul,
        OctonionMatrixEncodings.Zx, OctonionMatrixEncodings.dot3,
        OctonionMatrixEncodings.cross3]
    · simp [zornMul, OctonionMatrixEncodings.zornMul,
        OctonionMatrixEncodings.Zx, OctonionMatrixEncodings.dot3]

/-- In the concrete split-octonion Zorn model, norm-nullness does not imply
square-zero nilpotence. -/
theorem norm_null_does_not_imply_square_zero :
    ¬ ∀ x : ZornMatrix, zornNorm x = 0 → zornMul x x = ZornMatrix.zero := by
  rintro hall
  have hidem := (Zx_null_idempotent).2
  have hzero := hall OctonionMatrixEncodings.Zx (Zx_null_idempotent).1
  rw [hidem] at hzero
  have hne : OctonionMatrixEncodings.Zx ≠ ZornMatrix.zero := by
    intro h
    have ha := congrArg OctonionMatrixEncodings.Zorn.a h
    simp [ZornMatrix.zero, OctonionMatrixEncodings.Zx] at ha
  exact hne hzero

/-- The selected Zorn element is nonzero, nilpotent, and norm-null. -/
theorem split_octonion_nilpotent_identities :
    Z_mode ≠ ZornMatrix.zero ∧ zornMul Z_mode Z_mode = ZornMatrix.zero ∧ zornNorm Z_mode = 0 := by
  exact ⟨Z_mode_nonzero, Z_mode_nilpotent, Z_mode_null⟩

#check Z_mode_nonzero
#check Z_mode_nilpotent
#check Z_mode_null
#check split_octonion_nilpotent_identities

end SplitOctonionNilpotent
