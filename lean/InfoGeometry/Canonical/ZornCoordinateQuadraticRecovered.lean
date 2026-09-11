import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# ZornCoordinateQuadraticRecovered

Buildable recovery core extracted from the archived
`CanonicalZornCliffordRepresentation` fragment.

What is recovered here:
- the explicit eight-coordinate Zorn determinant
- the corresponding quadratic form on `Fin 8 → ℂ`

What is intentionally not claimed here:
- typed vector/spinor carriers
- Clifford generator actions
- spin-group representations
- the integral `II₄,₄` bridge

Those layers depend on owner modules and symbols that are not present in the
current repository checkout and therefore remain explicit restoration debt.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCoordinateQuadraticRecovered

/-- Zorn determinant in the recovered fixed eight-coordinate presentation. -/
def coordinateQuadraticFun (x : Fin 8 → ℂ) : ℂ :=
  x 0 * x 7 - x 1 * x 4 - x 2 * x 5 - x 3 * x 6

/-- The recovered coordinate Zorn determinant as a genuine quadratic form. -/
def coordinateQuadratic : QuadraticForm ℂ (Fin 8 → ℂ) :=
  QuadraticMap.ofPolar coordinateQuadraticFun
    (by
      intro c x
      simp [coordinateQuadraticFun]
      ring)
    (by
      intro x x' y
      simp [QuadraticMap.polar, coordinateQuadraticFun]
      ring)
    (by
      intro c x y
      simp [QuadraticMap.polar, coordinateQuadraticFun]
      ring)

@[simp] theorem coordinateQuadratic_apply (x : Fin 8 → ℂ) :
    coordinateQuadratic x = coordinateQuadraticFun x := by
  rfl

end InfoGeometry.Canonical.ZornCoordinateQuadraticRecovered

end noncomputable section
