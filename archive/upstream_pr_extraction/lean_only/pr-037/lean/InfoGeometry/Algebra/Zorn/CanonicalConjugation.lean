import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# Canonical conjugation on the real Zorn carrier

This file transports the already proved `ZornVectorMatrix` conjugation to the
canonical real Zorn carrier.  In particular, multiplication reversal is a
consequence of the native theorem `ZornVectorMatrix.conj_mul`.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

open InfoGeometry.Algebra

/-- Canonical split-octonion conjugation transported through the coordinate
equivalence with the native vector-matrix carrier. -/
def canonicalConj (X : CZ) : CZ :=
  canonicalVectorEquiv.symm (ZornVectorMatrix.conj (canonicalVectorEquiv X))

@[simp] theorem canonicalVectorEquiv_canonicalConj (X : CZ) :
    canonicalVectorEquiv (canonicalConj X) =
      ZornVectorMatrix.conj (canonicalVectorEquiv X) := by
  simp [canonicalConj]

@[simp] theorem canonicalConj_zero : canonicalConj (0 : CZ) = 0 := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_zero,
    ZornVectorMatrix.conj_zero]

@[simp] theorem canonicalConj_one : canonicalConj (1 : CZ) = 1 := by
  change canonicalConj ({ a := 1, b := 1, x := 0, y := 0 } : CZ) =
    ({ a := 1, b := 1, x := 0, y := 0 } : CZ)
  simp [canonicalConj, canonicalVectorEquiv, ZornVectorMatrix.conj]
  funext i
  rfl

@[simp] theorem canonicalConj_add (X Y : CZ) :
    canonicalConj (X + Y) = canonicalConj X + canonicalConj Y := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_add,
    ZornVectorMatrix.conj_add]

@[simp] theorem canonicalConj_sub (X Y : CZ) :
    canonicalConj (X - Y) = canonicalConj X - canonicalConj Y := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_sub,
    ZornVectorMatrix.conj_sub]

@[simp] theorem canonicalConj_smul (r : ℝ) (X : CZ) :
    canonicalConj (r • X) = r • canonicalConj X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_smul,
    ZornVectorMatrix.conj_smul]

@[simp] theorem canonicalConj_involutive (X : CZ) :
    canonicalConj (canonicalConj X) = X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, ZornVectorMatrix.conj_conj]

/-- Canonical conjugation reverses the actual nonassociative Zorn product. -/
theorem canonicalConj_mul (X Y : CZ) :
    canonicalConj (X * Y) = canonicalConj Y * canonicalConj X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_mul,
    ZornVectorMatrix.conj_mul]

end InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
