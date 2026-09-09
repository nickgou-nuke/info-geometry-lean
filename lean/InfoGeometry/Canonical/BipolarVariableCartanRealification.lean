import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import Mathlib

/-!
# Realification of the variable bipolar Cartan connection

The punctured complex plane is one-dimensional over `C` but two-dimensional as
a real manifold.  The holomorphic connection owner uses a complex-linear
one-form.  This file records its restriction to the real tangent carrier and
proves flatness there as a genuine real alternating two-form calculation.

The vanishing is not inferred merely from `Λ²_C C = 0`.  Instead:

* the base derivative alternation is zero because multiplication by the
  holomorphic derivative is symmetric in the two real tangent directions;
* the operator wedge is zero because all values lie in the same abelian Cartan
  line.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarVariableCartanRealification

open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The same point-dependent connection, restricted to real scalar
multiplication on the tangent complex plane. -/
def realVariableCartanConnection (s : ℂ) : Op1Form ℝ ℂ Matrix2C where
  toFun v := ((omegaCoeff s * v) / 2) • σ3c
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_add, add_smul, σ3c, Matrix.smul_apply] <;>
      ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ3c, Matrix.smul_apply, smul_smul] <;>
      push_cast <;>
      ring

@[simp] theorem realVariableCartanConnection_apply
    (s v : ℂ) :
    realVariableCartanConnection s v =
      ((omegaCoeff s * v) / 2) • σ3c :=
  by rfl

/-- The real-tangent operator self-wedge vanishes on every pair. -/
theorem realVariableCartanConnection_selfWedge_zero (s : ℂ) :
    wedge (realVariableCartanConnection s)
      (realVariableCartanConnection s) = 0 := by
  apply Op2Form.ext
  intro u v
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedge_apply, realVariableCartanConnection,
      σ3c, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;>
    ring

/-- Directional derivative coefficient on the real tangent carrier. -/
def realConnectionDirectionalDerivative
    (s u v : ℂ) : Matrix2C :=
  ((omegaCoeffDeriv s * u * v) / 2) • σ3c

/-- Alternation of the two real base directions. -/
def realVariableExteriorDerivativeAt
    (s u v : ℂ) : Matrix2C :=
  realConnectionDirectionalDerivative s u v -
    realConnectionDirectionalDerivative s v u

/-- The real exterior derivative contribution vanishes by the symmetry of the
complex-linear directional derivative. -/
@[simp] theorem realVariableExteriorDerivativeAt_eq_zero
    (s u v : ℂ) :
    realVariableExteriorDerivativeAt s u v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realVariableExteriorDerivativeAt,
      realConnectionDirectionalDerivative, σ3c,
      Matrix.smul_apply] <;>
    ring

/-- Bundled real exterior derivative form. -/
def realVariableExteriorDerivativeForm
    (s : ℂ) : Op2Form ℝ ℂ Matrix2C where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => realVariableExteriorDerivativeAt s u v
      map_add' := by intro v w; simp
      map_smul' := by intro c v; simp
    }
    map_add' := by intro u v; ext w; simp
    map_smul' := by intro c u; ext v; simp
  }
  alt' := by intro u; simp

/-- The bundled real exterior derivative is zero. -/
theorem realVariableExteriorDerivativeForm_eq_zero (s : ℂ) :
    realVariableExteriorDerivativeForm s = 0 := by
  apply Op2Form.ext
  intro u v
  simp [realVariableExteriorDerivativeForm]

/-- Realified curvature of the variable Cartan connection. -/
def realVariableCartanCurvatureForm
    (s : ℂ) : Op2Form ℝ ℂ Matrix2C :=
  realVariableExteriorDerivativeForm s +
    wedge (realVariableCartanConnection s)
      (realVariableCartanConnection s)

/-- Flatness of the variable connection on the real two-dimensional tangent
carrier. -/
theorem realVariableCartanCurvatureForm_eq_zero (s : ℂ) :
    realVariableCartanCurvatureForm s = 0 := by
  rw [realVariableCartanCurvatureForm,
    realVariableExteriorDerivativeForm_eq_zero,
    realVariableCartanConnection_selfWedge_zero]
  apply Op2Form.ext
  intro u v
  change (0 : Matrix2C) + 0 = 0
  simp only [add_zero]

/-- Compact realification packet. -/
theorem bipolar_variable_cartan_realification_packet (s : ℂ) :
    (∀ v, realVariableCartanConnection s v =
      variableCartanConnection s v) ∧
      realVariableExteriorDerivativeForm s = 0 ∧
      wedge (realVariableCartanConnection s)
        (realVariableCartanConnection s) = 0 ∧
      realVariableCartanCurvatureForm s = 0 := by
  exact ⟨by intro v; rfl,
    realVariableExteriorDerivativeForm_eq_zero s,
    realVariableCartanConnection_selfWedge_zero s,
    realVariableCartanCurvatureForm_eq_zero s⟩

end InfoGeometry.Canonical.BipolarVariableCartanRealification
