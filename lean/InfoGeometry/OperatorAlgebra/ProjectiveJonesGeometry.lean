/-
InfoGeometry/OperatorAlgebra/ProjectiveJonesGeometry.lean

Projective Jones geometry.

This module records the operatorial lift of Jones calculus:

  P ↦ U P U⁻¹.

It is a transport law for projective polarization projectors, not the
primitive source of the Poincare metric or the KMS theorem.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge

noncomputable section

namespace ProjectiveJonesGeometry

/-! ## 1. Operatorial Jones transforms -/

/--
An invertible operatorial Jones transform.

The projective action is conjugation by the unit `U`.
-/
structure OperatorialJonesTransform
    (Op : Type*) [Monoid Op] where
  /-- Jones transport unit. -/
  U : Units Op

namespace OperatorialJonesTransform

variable {Op : Type*} [Monoid Op]
variable (T : OperatorialJonesTransform Op)

/-- Operatorial projective action `x ↦ U x U⁻¹`. -/
def act
    (x : Op) : Op :=
  T.U.val * x * T.U.inv

@[simp]
theorem act_one :
    T.act 1 = 1 := by
  simp [act]

end OperatorialJonesTransform

/-! ## 2. Cartan axis and chiral/polarization poles -/

/--
Cartan/chiral axis for a two-state projective Jones geometry.

`chi` is the axis operator.  `P_left` and `P_right` are the two pole
projectors, supplied proof-carryingly so this socket does not depend on a
particular scalar normalization.
-/
structure JonesCartanAxis
    (Op : Type*) [Ring Op] [Module ℝ Op] where
  /-- Cartan/chiral eigenoperator. -/
  chi : Op

  /-- Axis involution law. -/
  chi_sq :
    chi * chi = 1

  /-- Left/north-pole projector. -/
  P_left : Op

  /-- Right/south-pole projector. -/
  P_right : Op

  /-- Left pole is idempotent. -/
  P_left_idem :
    P_left * P_left = P_left

  /-- Right pole is idempotent. -/
  P_right_idem :
    P_right * P_right = P_right

  /-- Pole projectors are complementary. -/
  complementary :
    P_left + P_right = 1

  /-- Left then right vanishes. -/
  left_right_zero :
    P_left * P_right = 0

  /-- Right then left vanishes. -/
  right_left_zero :
    P_right * P_left = 0

/-! ## 3. Axis-preserving Jones calculus -/

/--
Operatorial Jones calculus preserving a chosen Cartan axis.

This is the projective transport branch where conjugation by `U` fixes the
circular/chiral axis.
-/
structure OperatorialJonesCalculus
    (Op : Type*) [Ring Op] [Module ℝ Op]
    (C : JonesCartanAxis Op) where
  /-- Underlying Jones transform. -/
  transform : OperatorialJonesTransform Op

  /-- The Jones unit commutes with the Cartan axis. -/
  preserves_axis :
    transform.U.val * C.chi = C.chi * transform.U.val

namespace OperatorialJonesCalculus

variable {Op : Type*} [Ring Op] [Module ℝ Op]
variable {C : JonesCartanAxis Op}
variable (Jc : OperatorialJonesCalculus Op C)

/--
An axis-preserving Jones transport fixes the Cartan/chiral axis under
projective conjugation.
-/
theorem act_chi :
    Jc.transform.act C.chi = C.chi := by
  dsimp [OperatorialJonesTransform.act]
  calc
    Jc.transform.U.val * C.chi * Jc.transform.U.inv
        = C.chi * Jc.transform.U.val * Jc.transform.U.inv := by
            rw [Jc.preserves_axis]
    _ = C.chi * (Jc.transform.U.val * Jc.transform.U.inv) := by
            rw [mul_assoc]
    _ = C.chi * 1 := by
            rw [Jc.transform.U.val_inv]
    _ = C.chi := by
            rw [mul_one]

end OperatorialJonesCalculus

/-! ## 4. Optional Krein/J-unitary calibration -/

/-- Real bounded endomorphisms. -/
abbrev RealEnd
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/--
Jones transform with a Krein/J-unitary calibration.

Ordinary Jones transports are not forced to be J-unitary.  This optional
branch is for the real doubled Krein/CPT setting.
-/
structure KreinJonesTransform
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Adjoint backend. -/
  adjDatum :
    TopologicalCharge.AdjointDatum (RealEnd H)

  /-- Determinant backend compatible with the adjoint. -/
  detDatum :
    TopologicalCharge.AdjointDeterminantDatum (RealEnd H) adjDatum

  /-- Krein metric/fundamental symmetry operator. -/
  Jmetric : RealEnd H

  /-- Jones/Bogoliubov transport. -/
  U : RealEnd H

  /-- J-unitary calibration. -/
  is_junitary :
    TopologicalCharge.IsJUnitary adjDatum Jmetric U

end ProjectiveJonesGeometry
