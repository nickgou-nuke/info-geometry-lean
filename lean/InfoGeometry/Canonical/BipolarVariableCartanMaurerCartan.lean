import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import Mathlib

/-!
# Variable bipolar Cartan connection and local Maurer--Cartan equation

The global logarithmic differential on the twice-punctured plane has coefficient

`omega(s) = 1 / s - 1 / (s - 1)`.

This file uses it to define the point-dependent Cartan-valued one-form

`A_s(v) = (omega(s) * v / 2) sigma3`.

Three levels are kept separate.

* `omega` is a meromorphic coefficient and has a genuine complex derivative on
  `C \ {0,1}`;
* the local exterior derivative is the alternation of the directional
  derivative of `A` and vanishes because that derivative is complex-linear in
  the two tangent arguments;
* the self-wedge vanishes because every value lies in the same abelian Cartan
  line.

Consequently the local curvature vanishes.  On a compatible logarithm branch,
the diagonal half-log lift supplies a local pure-gauge primitive.  Globally the
connection may still have the already formalized nontrivial period character;
no globally single-valued logarithm or gauge primitive is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarLocalConformalCoordinate
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Meromorphic coefficient of `dq/q` in the standard complex coordinate. -/
def omegaCoeff (s : ℂ) : ℂ :=
  s⁻¹ - (s - 1)⁻¹

/-- Complex derivative of the logarithmic coefficient away from the punctures. -/
def omegaCoeffDeriv (s : ℂ) : ℂ :=
  -(1 / s ^ 2) + 1 / (s - 1) ^ 2

/-- The coefficient agrees with the repository-owned logarithmic differential
on the twice-punctured domain. -/
theorem omegaCoeff_eq_dlog01 {s : ℂ} (hs : s ∈ punctured01) :
    omegaCoeff s = dlog01 s := by
  rw [dlog01_eq_one_div_mul hs]
  unfold omegaCoeff
  have hs0 : s ≠ 0 := hs.1
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have h1s : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  field_simp [hs0, hs1, h1s]
  ring

/-- Genuine complex derivative of the meromorphic coefficient on its domain. -/
theorem hasDerivAt_omegaCoeff {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt omegaCoeff (omegaCoeffDeriv s) s := by
  have h0 : HasDerivAt (fun z : ℂ => z⁻¹) (-(1 : ℂ) / s ^ 2) s := by
    convert (hasDerivAt_id s).inv hs.1 using 1 <;> ring
  have hsub : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have h1 :
      HasDerivAt (fun z : ℂ => (z - 1)⁻¹)
        (-(1 : ℂ) / (s - 1) ^ 2) s := by
    convert hsub.inv (sub_ne_zero.mpr hs.2) using 1 <;> ring
  convert h0.sub h1 using 1 <;>
    simp [omegaCoeff, omegaCoeffDeriv] <;>
    ring

/-- Point-dependent Cartan-valued one-form
`A_s(v) = (omega(s) v / 2) sigma3`. -/
def variableCartanConnection (s : ℂ) : Op1Form ℂ ℂ Matrix2C where
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
      ring

@[simp] theorem variableCartanConnection_apply (s v : ℂ) :
    variableCartanConnection s v = ((omegaCoeff s * v) / 2) • σ3c :=
  rfl

/-- The connection is exactly the global logarithmic differential tensored with
`σ3/2` on the punctured domain. -/
theorem variableCartanConnection_eq_dlog01
    {s : ℂ} (hs : s ∈ punctured01) (v : ℂ) :
    variableCartanConnection s v = ((dlog01 s * v) / 2) • σ3c := by
  rw [variableCartanConnection_apply, omegaCoeff_eq_dlog01 hs]

/-- All values of the variable connection lie in one abelian Cartan line, so
its operator self-wedge vanishes identically. -/
theorem variableCartanConnection_selfWedge_zero (s : ℂ) :
    wedge (variableCartanConnection s) (variableCartanConnection s) = 0 := by
  apply Op2Form.ext
  intro u v
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedge_apply, variableCartanConnection, σ3c,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    ring

/-- Directional derivative of the connection value in base direction `u`,
evaluated on tangent direction `v`. -/
def connectionDirectionalDerivative
    (s u v : ℂ) : Matrix2C :=
  ((omegaCoeffDeriv s * u * v) / 2) • σ3c

/-- The scalar coefficient used in the directional derivative is the actual
derivative of `omega` composed with the affine direction `u`. -/
theorem hasDerivAt_omegaCoeff_along
    {s : ℂ} (hs : s ∈ punctured01) (u : ℂ) :
    HasDerivAt (fun t : ℂ => omegaCoeff (s + t * u))
      (omegaCoeffDeriv s * u) 0 := by
  have hline : HasDerivAt (fun t : ℂ => s + t * u) u 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) (c := s)).add
        ((hasDerivAt_id (x := (0 : ℂ))).mul_const u) using 1 <;>
      simp
  have hs0 : s + 0 * u ∈ punctured01 := by simpa using hs
  have hcomp := (hasDerivAt_omegaCoeff hs0).comp 0 hline
  convert hcomp using 1 <;> simp [omegaCoeffDeriv]

/-- Local coordinate exterior derivative obtained by alternating the two
complex tangent directions. -/
def variableExteriorDerivativeAt
    (s u v : ℂ) : Matrix2C :=
  connectionDirectionalDerivative s u v -
    connectionDirectionalDerivative s v u

/-- The exterior derivative vanishes: the derivative is complex-bilinear in
`u,v`, hence its alternation is zero. -/
@[simp] theorem variableExteriorDerivativeAt_eq_zero
    (s u v : ℂ) :
    variableExteriorDerivativeAt s u v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [variableExteriorDerivativeAt, connectionDirectionalDerivative,
      σ3c, Matrix.smul_apply] <;>
    ring

/-- Local curvature of the point-dependent Cartan connection. -/
def variableCartanCurvatureAt
    (s u v : ℂ) : Matrix2C :=
  variableExteriorDerivativeAt s u v +
    wedge (variableCartanConnection s) (variableCartanConnection s) u v

/-- Nonconstant local Maurer--Cartan equation for the logarithmic Cartan
connection.  Both the derivative and bracket terms vanish separately. -/
theorem variableCartanMaurerCartan
    (s u v : ℂ) :
    variableCartanCurvatureAt s u v = 0 := by
  rw [variableCartanCurvatureAt, variableExteriorDerivativeAt_eq_zero,
    variableCartanConnection_selfWedge_zero]
  simp

/-- Differential of the diagonal half-log lift in tangent direction `v`,
written using the global logarithmic coefficient. -/
def halfLogLiftDifferential (s v : ℂ) : Matrix2C :=
  ((omegaCoeff s * v) / 2) •
    !![plusWeight s, 0;
       0, -minusWeight s]

/-- Local left Maurer--Cartan factorization.  This is an algebraic identity for
the actual half-log lift and its displayed differential. -/
theorem halfLogLiftInv_mul_differential
    (s v : ℂ) :
    halfLogLiftInv s * halfLogLiftDifferential s v =
      variableCartanConnection s v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLiftInv, halfLogLiftDifferential,
      variableCartanConnection, plusWeight_mul_minusWeight,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, σ3c,
      mul_comm, mul_left_comm, mul_assoc] <;>
    ring
  all_goals
    rw [show minusWeight s * plusWeight s = 1 by
      rw [mul_comm, plusWeight_mul_minusWeight]]
    ring

/-- On a compatible principal-log chart, the positive diagonal entry has the
expected analytic derivative. -/
theorem hasDerivAt_plusWeight
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt plusWeight
      (plusWeight s * (dlog01 s / 2)) s := by
  have hW : HasDerivAt bipolarLog (dlog01 s) s :=
    (local_conformal_packet hs hslit).1
  have hhalf :
      HasDerivAt (fun z : ℂ => bipolarLog z / 2) (dlog01 s / 2) s :=
    hW.div_const 2
  simpa [plusWeight] using
    (Complex.hasDerivAt_exp (bipolarLog s / 2)).comp s hhalf

/-- On the same chart, the negative diagonal entry has the opposite analytic
derivative. -/
theorem hasDerivAt_minusWeight
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt minusWeight
      (minusWeight s * (-dlog01 s / 2)) s := by
  have hW : HasDerivAt bipolarLog (dlog01 s) s :=
    (local_conformal_packet hs hslit).1
  have hneg :
      HasDerivAt (fun z : ℂ => -bipolarLog z / 2)
        (-dlog01 s / 2) s :=
    hW.neg.div_const 2
  simpa [minusWeight] using
    (Complex.hasDerivAt_exp (-bipolarLog s / 2)).comp s hneg

/-- Compact variable-connection packet. -/
theorem bipolar_variable_cartan_packet
    {s : ℂ} (hs : s ∈ punctured01) (u v : ℂ) :
    omegaCoeff s = dlog01 s ∧
      HasDerivAt omegaCoeff (omegaCoeffDeriv s) s ∧
      variableExteriorDerivativeAt s u v = 0 ∧
      wedge (variableCartanConnection s) (variableCartanConnection s) u v = 0 ∧
      variableCartanCurvatureAt s u v = 0 := by
  exact ⟨omegaCoeff_eq_dlog01 hs,
    hasDerivAt_omegaCoeff hs,
    variableExteriorDerivativeAt_eq_zero s u v,
    by rw [variableCartanConnection_selfWedge_zero]; rfl,
    variableCartanMaurerCartan s u v⟩

end InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
