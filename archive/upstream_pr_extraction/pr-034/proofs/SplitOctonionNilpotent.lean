import proofs.OctonionMatrixEncodings

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

/-- The selected Zorn element is nonzero, nilpotent, and norm-null. -/
theorem split_octonion_nilpotent_identities :
    Z_mode ≠ ZornMatrix.zero ∧ zornMul Z_mode Z_mode = ZornMatrix.zero ∧ zornNorm Z_mode = 0 := by
  exact ⟨Z_mode_nonzero, Z_mode_nilpotent, Z_mode_null⟩

#check Z_mode_nonzero
#check Z_mode_nilpotent
#check Z_mode_null
#check split_octonion_nilpotent_identities

end SplitOctonionNilpotent
