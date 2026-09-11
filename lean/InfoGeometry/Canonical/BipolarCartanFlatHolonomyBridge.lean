import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarSpinHolonomy
import Mathlib.Tactic

/-!
# Flat Cartan connection and spinorial holonomy

This file joins two theorem owners without conflating local curvature with
global monodromy.

The canonical constant-coefficient connection is

`A(v) = v_η Kboost + v_θ Kcirc
      = ((v_η + i v_θ)/2) σ3`.

All its values lie in one abelian Cartan line. Its exterior derivative is zero
in the constant-coefficient model and its operator self-wedge also vanishes,
so the modeled curvature is zero. Independently, the logarithmic period lattice
produces nontrivial half-Cartan holonomy: either elementary puncture loop gives
`-I₂`, while the combined loop gives `I₂`.

The central sign acts nontrivially on two-component spinors but trivially by
matrix conjugation. This is the exact finite double-cover distinction. No
smooth principal bundle or path-ordered exponential is constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge

open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone

/-- Unambiguous local matrix carrier. -/
abbrev Matrix2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Complex coordinate differential `v_η + i v_θ`. -/
def complexCoordinateDifferential (v : Tangent2) : ℂ :=
  (v 0 : ℂ) + (v 1 : ℂ) * Complex.I

@[simp] theorem complexCoordinateDifferential_eta :
    complexCoordinateDifferential etaTangent = 1 := by
  simp [complexCoordinateDifferential, etaTangent]

@[simp] theorem complexCoordinateDifferential_theta :
    complexCoordinateDifferential thetaTangent = Complex.I := by
  simp [complexCoordinateDifferential, thetaTangent]

/-- Exact coordinate-free value of the canonical Cartan connection. -/
theorem canonicalConnection_value (v : Tangent2) :
    operatorConnection Kboost Kcirc v =
      (complexCoordinateDifferential v / 2) • σ3c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorConnection, Kboost, Kcirc, complexCoordinateDifferential,
      σ3c, Matrix.smul_apply] <;>
    ring

/-- The canonical connection has zero algebraic self-wedge on every tangent
pair, not only on the coordinate basis. -/
theorem canonicalConnection_selfWedge_zero :
    wedge (operatorConnection Kboost Kcirc)
        (operatorConnection Kboost Kcirc) = 0 := by
  apply Op2Form.ext
  intro u v
  change
    operatorConnection Kboost Kcirc u * operatorConnection Kboost Kcirc v -
        operatorConnection Kboost Kcirc v * operatorConnection Kboost Kcirc u = 0
  rw [canonicalConnection_value, canonicalConnection_value]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [mul_comm (complexCoordinateDifferential v / 2)
    (complexCoordinateDifferential u / 2)]
  simp

/-- Exterior derivative in the finite constant-coefficient connection model. -/
def constantExteriorDerivative
    (_A : Op1Form ℝ Tangent2 Matrix2C) : Op2Form ℝ Tangent2 Matrix2C :=
  0

@[simp] theorem constantExteriorDerivative_apply
    (A : Op1Form ℝ Tangent2 Matrix2C) (u v : Tangent2) :
    constantExteriorDerivative A u v = 0 := by
  change (0 : Matrix2C) = 0
  rfl

/-- Curvature of a constant-coefficient operator connection in this finite
model: zero derivative term plus the operator self-wedge. -/
def constantConnectionCurvature
    (A : Op1Form ℝ Tangent2 Matrix2C) : Op2Form ℝ Tangent2 Matrix2C :=
  constantExteriorDerivative A + wedge A A

/-- Full modeled curvature of the canonical Cartan connection vanishes. -/
theorem canonicalConstantConnectionCurvature_zero :
    constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 := by
  rw [constantConnectionCurvature, canonicalConnection_selfWedge_zero]
  apply Op2Form.ext
  intro u v
  change (0 : Matrix2C) + 0 = 0
  simp

/-- In particular the coordinate curvature coefficient vanishes. -/
theorem canonicalConnection_coordinate_curvature_zero :
    constantConnectionCurvature (operatorConnection Kboost Kcirc)
        etaTangent thetaTangent = 0 := by
  rw [canonicalConstantConnectionCurvature_zero]
  rfl

/-- Two-component complex spinor carrier. -/
abbrev Spinor2 := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- Matrix action on a two-component spinor. -/
def spinorAction (M : Matrix2C) (ψ : Spinor2) : Spinor2 :=
  Matrix.mulVec M ψ

@[simp] theorem spinorAction_one (ψ : Spinor2) :
    spinorAction (1 : Matrix2C) ψ = ψ := by
  funext i
  simp [spinorAction]

@[simp] theorem spinorAction_neg_one (ψ : Spinor2) :
    spinorAction (-(1 : Matrix2C)) ψ = -ψ := by
  change Matrix.mulVec (-(1 : Matrix2C)) ψ = -ψ
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]

/-- One elementary winding changes the sign of every spinor. -/
theorem originHolonomy_spinor_sign (ψ : Spinor2) :
    spinorAction (spinHolonomy originWinding) ψ = -ψ := by
  rw [spinHolonomy_origin]
  exact spinorAction_neg_one ψ

/-- A second turn restores the original spinor. -/
theorem originHolonomy_spinor_two_turns (ψ : Spinor2) :
    spinorAction (spinHolonomy originWinding)
        (spinorAction (spinHolonomy originWinding) ψ) = ψ := by
  calc
    spinorAction (spinHolonomy originWinding)
        (spinorAction (spinHolonomy originWinding) ψ)
        = -(spinorAction (spinHolonomy originWinding) ψ) :=
          originHolonomy_spinor_sign _
    _ = -(-ψ) := by rw [originHolonomy_spinor_sign]
    _ = ψ := by simp

/-- The central one-turn sign is invisible in the adjoint matrix action. -/
theorem originHolonomy_adjoint_trivial (X : Matrix2C) :
    spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  rw [spinHolonomy_origin]
  simp

/-- The combined finite-puncture winding has identity action already before
passing to the adjoint representation. -/
theorem combinedHolonomy_spinor_trivial (ψ : Spinor2) :
    spinorAction (spinHolonomy (originWinding + oneWinding)) ψ = ψ := by
  rw [spinHolonomy_origin_add_one]
  exact spinorAction_one ψ

/-- Compact local-flat/global-monodromy packet. -/
theorem flat_connection_nontrivial_holonomy_packet :
    constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      spinHolonomy originWinding = -(1 : Matrix2C) ∧
      spinHolonomy originWinding ≠ (1 : Matrix2C) ∧
      spinHolonomy (originWinding + oneWinding) = 1 := by
  exact ⟨canonicalConstantConnectionCurvature_zero,
    spinHolonomy_origin,
    spinHolonomy_origin_ne_one,
    spinHolonomy_origin_add_one⟩

end InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
