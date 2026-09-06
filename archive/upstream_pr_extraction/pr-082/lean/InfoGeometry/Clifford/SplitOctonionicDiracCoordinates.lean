import InfoGeometry.Clifford.GogberashviliPaperConvention

/-!
# Coordinate and norm layer for the split-octonionic Dirac paper

This is the native formalization of equations (7)--(9) of arXiv:2409.13736:
the eight real coordinates, the paper conjugation, and the split quadratic
form.  Differential operators are deliberately not smuggled into this layer.
-/

namespace InfoGeometry.Clifford.SplitOctonionicDiracCoordinates

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

structure Coordinates where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ
  x5 : ℝ
  x6 : ℝ
  x7 : ℝ

def conjugate (x : Coordinates) : Coordinates :=
  { x0 := x.x0, x1 := -x.x1, x2 := -x.x2, x3 := -x.x3
    x4 := -x.x4, x5 := -x.x5, x6 := -x.x6, x7 := -x.x7 }

def quadratic (x : Coordinates) : ℝ :=
    x.x0 ^ 2 + x.x1 ^ 2 + x.x2 ^ 2 + x.x3 ^ 2 -
    x.x4 ^ 2 - x.x5 ^ 2 - x.x6 ^ 2 - x.x7 ^ 2

def bilinear (x y : Coordinates) : ℝ :=
  x.x0 * y.x0 + x.x1 * y.x1 + x.x2 * y.x2 + x.x3 * y.x3 -
    x.x4 * y.x4 - x.x5 * y.x5 - x.x6 * y.x6 - x.x7 * y.x7

noncomputable def zornPair (X Y : ZornCell ℝ) : ℝ :=
  (X.r * Y.s + X.s * Y.r - X.x1 * Y.y1 - X.y1 * Y.x1 -
    X.x2 * Y.y2 - X.y2 * Y.x2 - X.x3 * Y.y3 - X.y3 * Y.x3) / 2

def element (x : Coordinates) : ZornCell ℝ :=
  { r := x.x0 + x.x4
    s := x.x0 - x.x4
    x1 := -x.x1 + x.x5
    x2 := -x.x2 + x.x6
    x3 := -x.x3 + x.x7
    y1 := x.x1 + x.x5
    y2 := x.x2 + x.x6
    y3 := x.x3 + x.x7 }

def scalarElement (r : ℝ) : ZornCell ℝ :=
  { r := r, s := r, x1 := 0, x2 := 0, x3 := 0,
    y1 := 0, y2 := 0, y3 := 0 }

theorem conjugate_involutive (x : Coordinates) : conjugate (conjugate x) = x := by
  cases x <;> simp [conjugate]

theorem element_conjugate (x : Coordinates) :
    element (conjugate x) =
      { r := x.x0 - x.x4
        s := x.x0 + x.x4
        x1 := x.x1 - x.x5
        x2 := x.x2 - x.x6
        x3 := x.x3 - x.x7
        y1 := -x.x1 - x.x5
        y2 := -x.x2 - x.x6
        y3 := -x.x3 - x.x7 } := by
  simp only [element, conjugate] <;> ring

set_option maxHeartbeats 800000 in
theorem element_mul_conjugate (x : Coordinates) :
    element x * element (conjugate x) = scalarElement (quadratic x) := by
  change mulZ (element x) (element (conjugate x)) = scalarElement (quadratic x)
  apply zorn_ext <;>
    simp [element, conjugate, scalarElement, quadratic, ZornCell.mulZ, mulZ,
      InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ,
      InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ, negZ] <;>
    ring_nf

theorem quadratic_conjugate (x : Coordinates) :
    quadratic (conjugate x) = quadratic x := by
  cases x
  simp [quadratic, conjugate]

theorem bilinear_self (x : Coordinates) : bilinear x x = quadratic x := by
  simp [bilinear, quadratic]
  ring

theorem bilinear_symm (x y : Coordinates) : bilinear x y = bilinear y x := by
  simp [bilinear]
  ring

theorem element_pair (x y : Coordinates) :
    zornPair (element x) (element y) = bilinear x y := by
  simp [zornPair, element, bilinear]
  ring

end InfoGeometry.Clifford.SplitOctonionicDiracCoordinates
