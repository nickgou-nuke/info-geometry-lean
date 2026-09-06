import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.SplitOctonionQ

/-!
# Canonical Zorn / split-octonion carrier bridge

This file provides the minimal carrier-level bridge between the canonical
`ZornMatrix` record and the rational split-octonion carrier used in the
`SplitO` / `J₂(𝕆ₛ)` lane.

It does not assert any multiplication compatibility.  That would be a
stronger algebra theorem and is not needed for the current bridge.
-/

namespace InfoGeometry.Canonical.ZornSplitOctonionBridge

open InfoGeometry.Algebra.SplitOctonionQ

noncomputable def zornToSplitO (Z : ZornMatrix ℚ) : SplitO :=
  { a := Z.a
    b := Z.b
    x0 := Z.x 0
    x1 := Z.x 1
    x2 := Z.x 2
    y0 := Z.y 0
    y1 := Z.y 1
    y2 := Z.y 2 }

noncomputable def splitOToZorn (Z : SplitO) : ZornMatrix ℚ :=
  { a := Z.a
    b := Z.b
    x := ![Z.x0, Z.x1, Z.x2]
    y := ![Z.y0, Z.y1, Z.y2] }

noncomputable def splitOColorProject (Z : SplitO) : SplitO :=
  { a := 0
    b := 0
    x0 := Z.x0
    x1 := Z.x1
    x2 := Z.x2
    y0 := 0
    y1 := 0
    y2 := 0 }

noncomputable def splitOAnticolorProject (Z : SplitO) : SplitO :=
  { a := 0
    b := 0
    x0 := 0
    x1 := 0
    x2 := 0
    y0 := Z.y0
    y1 := Z.y1
    y2 := Z.y2 }

noncomputable def splitODiagonalProject (Z : SplitO) : SplitO :=
  { a := Z.a
    b := Z.b
    x0 := 0
    x1 := 0
    x2 := 0
    y0 := 0
    y1 := 0
    y2 := 0 }

@[simp] theorem zornToSplitO_colorProject (Z : ZornMatrix ℚ) :
    zornToSplitO (ZornMatrix.colorProject Z) =
      splitOColorProject (zornToSplitO Z) := by
  rw [ZornMatrix.colorProject_apply]
  simp [zornToSplitO, splitOColorProject]

@[simp] theorem zornToSplitO_anticolorProject (Z : ZornMatrix ℚ) :
    zornToSplitO (ZornMatrix.anticolorProject Z) =
      splitOAnticolorProject (zornToSplitO Z) := by
  rw [ZornMatrix.anticolorProject_apply]
  simp [zornToSplitO, splitOAnticolorProject]

@[simp] theorem splitOColorProject_idempotent (Z : SplitO) :
    splitOColorProject (splitOColorProject Z) = splitOColorProject Z := by
  rfl

@[simp] theorem splitOAnticolorProject_idempotent (Z : SplitO) :
    splitOAnticolorProject (splitOAnticolorProject Z) =
      splitOAnticolorProject Z := by
  rfl

theorem splitO_peirce_decomposition (Z : SplitO) :
    Z =
      splitODiagonalProject Z +
      splitOColorProject Z +
      splitOAnticolorProject Z := by
  cases Z
  ext <;> simp [splitODiagonalProject, splitOColorProject, splitOAnticolorProject, SplitO.add]

theorem zornToSplitO_peirce_decomposition (Z : ZornMatrix ℚ) :
    zornToSplitO Z =
      splitODiagonalProject (zornToSplitO Z) +
      splitOColorProject (zornToSplitO Z) +
      splitOAnticolorProject (zornToSplitO Z) := by
  cases Z
  ext <;> simp [zornToSplitO, splitODiagonalProject, splitOColorProject,
    splitOAnticolorProject, SplitO.add]

end InfoGeometry.Canonical.ZornSplitOctonionBridge
