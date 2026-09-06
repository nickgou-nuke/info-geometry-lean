import Mathlib.Tactic
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-!
# Quaternionic twistor sphere on the finite operator carrier

This file closes the finite algebraic part of the quaternionic twistor-sphere
claim used by the Pauli--Dirac soldering bridge.

For real coefficients `(a,b,c)`, the linear combination

`J_(a,b,c) = a I + b J + c K`

squares to `-(a^2+b^2+c^2)`.  Hence every point of the unit two-sphere gives
a genuine complex structure on the existing real four-dimensional carrier.

This is deliberately only the algebraic `S^2` of complex structures.  It does
not construct a bundle connection, Berry curvature, Berry holonomy, or a
smooth hyperkähler/twistor manifold.
-/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicTwistorSphere

open Matrix
open InfoGeometry.Canonical.BiQuaternionKahlerFinite
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-- The matrix representative of the quaternionic axis `a I + b J + c K`. -/
def twistorMatrix (a b c : ℝ) : Mat4 :=
  a • I4c + b • J4c + c • K4c

/-- The exact quadratic law before imposing the unit-sphere condition. -/
theorem twistorMatrix_sq (a b c : ℝ) :
    twistorMatrix a b c * twistorMatrix a b c =
      (-(a ^ 2 + b ^ 2 + c ^ 2)) • (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistorMatrix, I4c, J4c, K4c,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

/-- The same quaternionic axis as a genuine real-linear endomorphism. -/
def twistorAxis (a b c : ℝ) :
    Module.End ℝ QuaternionicPauliDiracSoldering.QuaternionicOperators.Carrier :=
  (twistorMatrix a b c).mulVecLin

/-- Operator form of the exact quadratic law. -/
theorem twistorAxis_sq (a b c : ℝ) :
    (twistorAxis a b c).comp (twistorAxis a b c) =
      (-(a ^ 2 + b ^ 2 + c ^ 2)) •
        (LinearMap.id : Module.End ℝ
          QuaternionicPauliDiracSoldering.QuaternionicOperators.Carrier) := by
  apply LinearMap.ext
  intro x
  change
    (twistorMatrix a b c).mulVec ((twistorMatrix a b c).mulVec x) =
      (-(a ^ 2 + b ^ 2 + c ^ 2)) • x
  rw [← Matrix.mulVec_mulVec, twistorMatrix_sq]
  simp

/-- Unit vectors in `R^3` parameterize the finite quaternionic twistor sphere. -/
def OnTwistorSphere (a b c : ℝ) : Prop :=
  a ^ 2 + b ^ 2 + c ^ 2 = 1

/-- Every point of the quaternionic twistor two-sphere is a complex structure:
its square is exactly `-Id`. -/
theorem twistorAxis_isComplexStructure
    {a b c : ℝ} (h : OnTwistorSphere a b c) :
    (twistorAxis a b c).comp (twistorAxis a b c) =
      -(LinearMap.id : Module.End ℝ
        QuaternionicPauliDiracSoldering.QuaternionicOperators.Carrier) := by
  rw [twistorAxis_sq, h]
  simp

/-- The three coordinate poles recover the existing quaternionic operators. -/
theorem twistorAxis_coordinate_packet :
    twistorAxis 1 0 0 =
        QuaternionicPauliDiracSoldering.QuaternionicOperators.I ∧
    twistorAxis 0 1 0 =
        QuaternionicPauliDiracSoldering.QuaternionicOperators.J ∧
    twistorAxis 0 0 1 =
        QuaternionicPauliDiracSoldering.QuaternionicOperators.K := by
  constructor
  · apply LinearMap.ext
    intro x
    simp [twistorAxis, twistorMatrix,
      QuaternionicPauliDiracSoldering.QuaternionicOperators.I]
  constructor
  · apply LinearMap.ext
    intro x
    simp [twistorAxis, twistorMatrix,
      QuaternionicPauliDiracSoldering.QuaternionicOperators.J]
  · apply LinearMap.ext
    intro x
    simp [twistorAxis, twistorMatrix,
      QuaternionicPauliDiracSoldering.QuaternionicOperators.K]

end InfoGeometry.Bridge.QuaternionicTwistorSphere
