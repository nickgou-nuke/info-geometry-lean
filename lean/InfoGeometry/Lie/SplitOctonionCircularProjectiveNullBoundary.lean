import InfoGeometry.Lie.SplitOctonionCircularCausalConeBridge
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
import InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence

/-!
# Projective circular null boundary

The circular `(4,4)` quadratic form descends to projective rays.  This owner
records only the algebraic projectivized null locus; it makes no identification
with a Minkowski conformal compactification or with a topological boundary.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary

open InfoGeometry.Lie.SplitOctonionCircularCausalConeBridge
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
open InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
open InfoGeometry.Twistor

abbrev Coord := Fin 8 → ℝ
abbrev CircularProjective := ℙ ℝ Coord

/-- Projectivized circular null cone. -/
abbrev CircularNullBoundary := TwistorSpace circularPeirceQuadratic

/-- A nonzero circular null representative defines a projective boundary point. -/
noncomputable def circularNullBoundaryMk
    (x : Coord) (hx : x ≠ 0) (hQ : circularPeirceQuadratic x = 0) :
    CircularNullBoundary :=
  twistorMk circularPeirceQuadratic x hx hQ

@[simp] theorem circularNullBoundaryMk_val
    (x : Coord) (hx : x ≠ 0) (hQ : circularPeirceQuadratic x = 0) :
    (circularNullBoundaryMk x hx hQ).1 = Projectivization.mk ℝ x hx := by
  rfl

theorem circularProjectiveNull_mk_iff
    (x : Coord) (hx : x ≠ 0) :
    InfoGeometry.Twistor.IsNull circularPeirceQuadratic
        (Projectivization.mk ℝ x hx) ↔
      circularPeirceQuadratic x = 0 := by
  exact isNull_mk_iff circularPeirceQuadratic x hx

theorem circularProjectiveNull_mk_iff_witt
    (x : Coord) (hx : x ≠ 0) :
    InfoGeometry.Twistor.IsNull circularPeirceQuadratic
        (Projectivization.mk ℝ x hx) ↔
      circularWittQuadratic x = 0 := by
  rw [circularProjectiveNull_mk_iff]
  rw [circularPeirceQuadratic_formula]
  simp [circularWittQuadratic]

theorem circularNullBoundaryMk_eq_iff
    (x y : Coord) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxQ : circularPeirceQuadratic x = 0)
    (hyQ : circularPeirceQuadratic y = 0) :
    circularNullBoundaryMk x hx hxQ = circularNullBoundaryMk y hy hyQ ↔
      ∃ a : ℝ, a ≠ 0 ∧ y = a • x := by
  have heq : circularNullBoundaryMk x hx hxQ = circularNullBoundaryMk y hy hyQ ↔
      Projectivization.mk ℝ x hx = Projectivization.mk ℝ y hy := Subtype.ext_iff
  rw [heq]
  rw [Projectivization.mk_eq_mk_iff ℝ x y hx hy]
  constructor
  · rintro ⟨a, h⟩
    use (a⁻¹ : ℝˣ).val
    refine ⟨Units.ne_zero _, ?_⟩
    calc y = (1 : ℝ) • y := by simp
      _ = ((a⁻¹ : ℝˣ).val * (a : ℝˣ).val) • y := by simp
      _ = (a⁻¹ : ℝˣ).val • (a : ℝˣ).val • y := by rw [mul_smul]
      _ = (a⁻¹ : ℝˣ).val • x := by rw [←h]; rfl
  · rintro ⟨a, ha, h⟩
    use (Units.mk0 a ha)⁻¹
    calc (Units.mk0 a ha)⁻¹.val • y = (a⁻¹ : ℝ) • a • x := by exact congrArg (HSMul.hSMul (Units.mk0 a ha)⁻¹.val) h
      _ = ((a⁻¹ : ℝ) * a) • x := by rw [mul_smul]
      _ = (1 : ℝ) • x := by rw [inv_mul_cancel₀ ha]
      _ = x := by simp

theorem circularNullBoundary_diagonal_minkowski_iff
    (v : Minkowski4)
    (hv : minkowskiDiagonalEmbedding (minkowskiCoordinates v) ≠ 0) :
    InfoGeometry.Twistor.IsNull circularPeirceQuadratic
        (Projectivization.mk ℝ
          (minkowskiDiagonalEmbedding (minkowskiCoordinates v)) hv) ↔
      v.IsNull := by
  rw [circularProjectiveNull_mk_iff]
  exact circularPeirceQuadratic_diagonal_eq_minkowski_q v ▸ Iff.rfl

end InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary
