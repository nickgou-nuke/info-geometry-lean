import InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Horizontal Souriau flow in the centered zeta chart

This owner formalizes the finite algebraic shadow of the normal flow
`(u,v) ↦ (u + a,v)`.  It records the flow law and its conjugation by the
existing `V₄` chart symmetries.  No analytic zeta gradient, Hessian, or
thermodynamic limit is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaSouriauHorizontalFlow

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics

abbrev Chart := ZetaCenteredChart

/-- Horizontal/normal translation in the centered zeta chart. -/
def horizontalTranslation (a : ℝ) (x : Chart) : Chart :=
  ⟨x.u + a, x.v⟩

/-- Sign character for the normal flow under the finite `V₄` frame. -/
def zetaNormalSign : ChartSymmetry → ℝ
  | ChartSymmetry.identity => 1
  | ChartSymmetry.conjugation => 1
  | ChartSymmetry.functionalDual => -1
  | ChartSymmetry.criticalMirror => -1

@[simp] theorem zetaNormalSign_sq (g : ChartSymmetry) :
    zetaNormalSign g * zetaNormalSign g = 1 := by
  cases g <;> norm_num [zetaNormalSign]

theorem zetaNormalSign_compose (g h : ChartSymmetry) :
    zetaNormalSign (chartSymmetryCompose g h) =
      zetaNormalSign g * zetaNormalSign h := by
  cases g <;> cases h <;> norm_num [zetaNormalSign, chartSymmetryCompose]

@[simp] theorem horizontalTranslation_zero (x : Chart) :
    horizontalTranslation 0 x = x := by
  ext <;> simp [horizontalTranslation]

theorem horizontalTranslation_add (a b : ℝ) (x : Chart) :
    horizontalTranslation a (horizontalTranslation b x) =
      horizontalTranslation (a + b) x := by
  apply ZetaCenteredChart.ext
  · simp [horizontalTranslation]
    ring
  · rfl

theorem horizontalTranslation_inverse (a : ℝ) (x : Chart) :
    horizontalTranslation (-a) (horizontalTranslation a x) = x := by
  rw [horizontalTranslation_add]
  simp [horizontalTranslation, add_comm]

@[simp] theorem horizontalTranslation_preserves_v (a : ℝ) (x : Chart) :
    (horizontalTranslation a x).v = x.v := rfl

/-- The normal coordinate is translated by exactly the flow parameter. -/
theorem horizontalTranslation_u (a : ℝ) (x : Chart) :
    (horizontalTranslation a x).u = x.u + a := rfl

theorem horizontalTranslation_heightTranslation_commute
    (a b : ℝ) (x : Chart) :
    horizontalTranslation a (heightTranslation b x) =
      heightTranslation b (horizontalTranslation a x) := by
  rfl

theorem conjugation_conjugates_horizontalTranslation
    (a : ℝ) (x : Chart) :
    conjugation (horizontalTranslation a x) =
      horizontalTranslation a (conjugation x) := by
  rfl

theorem functionalDual_reverses_horizontalTranslation
    (a : ℝ) (x : Chart) :
    functionalDual (horizontalTranslation a x) =
      horizontalTranslation (-a) (functionalDual x) := by
  ext <;> simp [functionalDual, horizontalTranslation]
  ring

theorem criticalMirror_reverses_horizontalTranslation
    (a : ℝ) (x : Chart) :
    criticalMirror (horizontalTranslation a x) =
      horizontalTranslation (-a) (criticalMirror x) := by
  ext <;> simp [criticalMirror, horizontalTranslation]
  ring

/-- The finite `V₄` frame conjugates the horizontal flow by `zetaNormalSign`. -/
theorem centeredChartSymmetryAct_horizontalTranslation
    (g : ChartSymmetry) (a : ℝ) (x : Chart) :
    centeredChartSymmetryAct g (horizontalTranslation a x) =
      horizontalTranslation (zetaNormalSign g * a)
        (centeredChartSymmetryAct g x) := by
  cases g <;> cases x <;>
    simp [centeredChartSymmetryAct, zetaNormalSign, horizontalTranslation,
      conjugation, functionalDual, criticalMirror] <;>
    ring

/-- The horizontal vector-field readout is the constant normal direction. -/
def horizontalFlowField (_x : Chart) : Chart := ⟨1, 0⟩

@[simp] theorem horizontalFlowField_readout (x : Chart) :
    horizontalFlowField x = ⟨1, 0⟩ := rfl

end InfoGeometry.Arithmetic.ZetaSouriauHorizontalFlow
