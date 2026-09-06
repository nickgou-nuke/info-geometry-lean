import InfoGeometry.Algebra.Zorn.Basic

/-!
# InfoGeometry.Algebra.Zorn.NullCone

Canonical null representatives in the local Zorn/split-octonion cell.

These are representative-level determinant-zero facts.  They do not use
projective quotienting.
-/

namespace InfoGeometry.Algebra.Zorn

variable {R : Type*} [CommRing R]

/-- Upper diagonal Peirce projector. -/
def pPlus : ZornMatrix R where
  a := 1
  b := 0
  x := 0
  y := 0

/-- Lower diagonal Peirce projector. -/
def pMinus : ZornMatrix R where
  a := 0
  b := 1
  x := 0
  y := 0

/-- Upper off-diagonal lightray. -/
def upperLightray (v : Fin 3 → R) : ZornMatrix R where
  a := 0
  b := 0
  x := v
  y := 0

/-- Lower off-diagonal lightray. -/
def lowerLightray (w : Fin 3 → R) : ZornMatrix R where
  a := 0
  b := 0
  x := 0
  y := w

/-- The upper diagonal sector `p₊` lies on the Zorn null quadric. -/
@[simp]
theorem detZ_pPlus (cp : CrossProduct3 R) :
    ZornMatrix.detZ cp (pPlus : ZornMatrix R) = 0 := by
  simp [ZornMatrix.detZ, pPlus, cp.dot_zero_left]

/-- The lower diagonal sector `p₋` lies on the Zorn null quadric. -/
@[simp]
theorem detZ_pMinus (cp : CrossProduct3 R) :
    ZornMatrix.detZ cp (pMinus : ZornMatrix R) = 0 := by
  simp [ZornMatrix.detZ, pMinus, cp.dot_zero_left]

/-- Every upper off-diagonal arrow is Zorn-null. -/
@[simp]
theorem detZ_upperLightray
    (cp : CrossProduct3 R) (v : Fin 3 → R) :
    ZornMatrix.detZ cp (upperLightray v) = 0 := by
  simp [ZornMatrix.detZ, upperLightray, cp.dot_zero_right]

/-- Every lower off-diagonal arrow is Zorn-null. -/
@[simp]
theorem detZ_lowerLightray
    (cp : CrossProduct3 R) (w : Fin 3 → R) :
    ZornMatrix.detZ cp (lowerLightray w) = 0 := by
  simp [ZornMatrix.detZ, lowerLightray, cp.dot_zero_left]

/-- `p₊` is null. -/
@[simp]
theorem pPlus_isNull (cp : CrossProduct3 R) :
    ZornMatrix.IsNull cp (pPlus : ZornMatrix R) := by
  exact detZ_pPlus cp

/-- `p₋` is null. -/
@[simp]
theorem pMinus_isNull (cp : CrossProduct3 R) :
    ZornMatrix.IsNull cp (pMinus : ZornMatrix R) := by
  exact detZ_pMinus cp

/-- Every upper lightray is null. -/
@[simp]
theorem upperLightray_isNull
    (cp : CrossProduct3 R) (v : Fin 3 → R) :
    ZornMatrix.IsNull cp (upperLightray v) := by
  exact detZ_upperLightray cp v

/-- Every lower lightray is null. -/
@[simp]
theorem lowerLightray_isNull
    (cp : CrossProduct3 R) (w : Fin 3 → R) :
    ZornMatrix.IsNull cp (lowerLightray w) := by
  exact detZ_lowerLightray cp w

end InfoGeometry.Algebra.Zorn
