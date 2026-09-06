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
theorem detZ_pPlus :
    ZornMatrix.detZ (pPlus : ZornMatrix R) = 0 := by
  simp [ZornMatrix.detZ, pPlus, InfoGeometry.Canonical.ZornMatrix.dot]

/-- The lower diagonal sector `p₋` lies on the Zorn null quadric. -/
@[simp]
theorem detZ_pMinus :
    ZornMatrix.detZ (pMinus : ZornMatrix R) = 0 := by
  simp [ZornMatrix.detZ, pMinus, InfoGeometry.Canonical.ZornMatrix.dot]

/-- Every upper off-diagonal arrow is Zorn-null. -/
@[simp]
theorem detZ_upperLightray (v : Fin 3 → R) :
    ZornMatrix.detZ (upperLightray v) = 0 := by
  simp [ZornMatrix.detZ, upperLightray, InfoGeometry.Canonical.ZornMatrix.dot]

/-- Every lower off-diagonal arrow is Zorn-null. -/
@[simp]
theorem detZ_lowerLightray (w : Fin 3 → R) :
    ZornMatrix.detZ (lowerLightray w) = 0 := by
  simp [ZornMatrix.detZ, lowerLightray, InfoGeometry.Canonical.ZornMatrix.dot]

/-- `p₊` is null. -/
@[simp]
theorem pPlus_isNull :
    ZornMatrix.IsNull (pPlus : ZornMatrix R) := by
  exact detZ_pPlus

/-- `p₋` is null. -/
@[simp]
theorem pMinus_isNull :
    ZornMatrix.IsNull (pMinus : ZornMatrix R) := by
  exact detZ_pMinus

/-- Every upper lightray is null. -/
@[simp]
theorem upperLightray_isNull (v : Fin 3 → R) :
    ZornMatrix.IsNull (upperLightray v) := by
  exact detZ_upperLightray v

/-- Every lower lightray is null. -/
@[simp]
theorem lowerLightray_isNull (w : Fin 3 → R) :
    ZornMatrix.IsNull (lowerLightray w) := by
  exact detZ_lowerLightray w

end InfoGeometry.Algebra.Zorn
