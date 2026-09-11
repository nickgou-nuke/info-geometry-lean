import InfoGeometry.Clifford.SplitOctonionicDiracCoordinates
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic split-octonionic Dirac operator

This is the native algebraic content of equations (13)--(16) of
arXiv:2409.13736 after the paper's stated restriction to the four active
variables.  The four derivative coefficients are parameters; analytic
differentiation is not assumed.
-/

namespace InfoGeometry.Clifford.SplitOctonionicDiracEquation

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Clifford.GogberashviliPaperConvention
open InfoGeometry.Clifford.SplitOctonionicDiracCoordinates
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

structure DerivativeData where
  dt : ℝ
  dx : ℝ
  dy : ℝ
  dz : ℝ

def operator (d : DerivativeData) : ZornCell ℝ :=
  element
    { x0 := 0, x1 := -d.dx, x2 := -d.dy, x3 := -d.dz,
      x4 := d.dt, x5 := 0, x6 := 0, x7 := 0 }

def massOperator (m : ℝ) : ZornCell ℝ :=
  m • paperJ 2

def potential (φ A1 A2 A3 : ℝ) : ZornCell ℝ :=
  InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ
    (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ φ paperI)
    (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ
      (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ A1 (paperj 0))
      (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ
        (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ A2 (paperj 1))
        (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ A3 (paperj 2))))

def residual (d : DerivativeData) (m : ℝ) (ψ : Coordinates) : ZornCell ℝ :=
  (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ
    (operator d) (negZ (massOperator m))) * element ψ

noncomputable def lagrangian (d : DerivativeData) (m : ℝ) (ψ : Coordinates) : ℝ :=
  zornPair (paperJ 2 * element ψ)
      (operator d * element ψ) / 2 + m * bilinear ψ ψ / 2

theorem operator_coordinate (d : DerivativeData) :
    operator d =
      { r := d.dt, s := -d.dt,
        x1 := d.dx, x2 := d.dy, x3 := d.dz,
        y1 := -d.dx, y2 := -d.dy, y3 := -d.dz } := by
  simp [operator, element, sub_eq_add_neg]
  <;> ring

theorem massOperator_coordinate (m : ℝ) :
    massOperator m =
      { r := 0, s := 0,
        x1 := 0, x2 := 0, x3 := m,
        y1 := 0, y2 := 0, y3 := m } := by
  change smulZ m (paperJ 2) = _
  apply zorn_ext <;>
    dsimp [paperJ, J, smulZ] <;> ring

theorem residual_eq_zero_iff (d : DerivativeData) (m : ℝ) (ψ : Coordinates) :
    residual d m ψ = 0 ↔
      (residual d m ψ).r = 0 ∧ (residual d m ψ).s = 0 ∧
      (residual d m ψ).x1 = 0 ∧ (residual d m ψ).x2 = 0 ∧
      (residual d m ψ).x3 = 0 ∧ (residual d m ψ).y1 = 0 ∧
      (residual d m ψ).y2 = 0 ∧ (residual d m ψ).y3 = 0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg ZornCell.r h,
      by simpa using congrArg ZornCell.s h,
      by simpa using congrArg ZornCell.x1 h,
      by simpa using congrArg ZornCell.x2 h,
      by simpa using congrArg ZornCell.x3 h,
      by simpa using congrArg ZornCell.y1 h,
      by simpa using congrArg ZornCell.y2 h,
      by simpa using congrArg ZornCell.y3 h⟩
  · rintro ⟨hr, hs, hx1, hx2, hx3, hy1, hy2, hy3⟩
    apply zorn_ext
    · exact hr
    · exact hs
    · exact hx1
    · exact hx2
    · exact hx3
    · exact hy1
    · exact hy2
    · exact hy3

theorem algebraic_dirac_equation (d : DerivativeData) (m : ℝ) (ψ : Coordinates) :
    residual d m ψ = 0 ↔
      (InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ
        (operator d) (negZ (massOperator m))) * element ψ = 0 := by
  rfl

theorem potential_coordinate (φ A1 A2 A3 : ℝ) :
    potential φ A1 A2 A3 =
      { r := φ, s := -φ,
        x1 := -A1, x2 := -A2, x3 := -A3,
        y1 := A1, y2 := A2, y3 := A3 } := by
  apply zorn_ext <;>
    dsimp [potential, paperI, paperj, I, j,
      InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.smulZ,
      InfoGeometry.Clifford.GogberashviliSplitOctonionBasis.addZ, negZ] <;> ring

theorem lagrangian_mass_term (d : DerivativeData) (m : ℝ) (ψ : Coordinates) :
    lagrangian d m ψ - zornPair (paperJ 2 * element ψ) (operator d * element ψ) / 2 =
      m * bilinear ψ ψ / 2 := by
  simp [lagrangian]

end InfoGeometry.Clifford.SplitOctonionicDiracEquation
