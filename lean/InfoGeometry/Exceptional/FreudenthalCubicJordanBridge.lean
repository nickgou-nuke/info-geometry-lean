/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.Freudenthal

/-!
# Gap 5: Freudenthal Triple → Cubic Jordan Bridge

Connects `FreudenthalCharge` to `CubicJordanDatum` via the quartic invariant
and symplectic form. -/

namespace InfoGeometry.Exceptional.FreudenthalCubicJordanBridge

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Exceptional.Freudenthal.CubicJordanDatum
open InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The trace pairing from a `CubicJordanDatum` is symmetric. -/
theorem trace_comm_symm (D : CubicJordanDatum J) (x y : J) :
    D.traceBilin x y = D.traceBilin y x :=
  D.trace_comm x y

/-- The trilinear form is symmetric in the first two arguments. -/
theorem normTrilin_swap₁₂ (D : CubicJordanDatum J) (x y z : J) :
    D.normTrilin x y z = D.normTrilin y x z :=
  D.normTrilin_swap₁₂ x y z

/-- The trilinear form is symmetric in the last two arguments. -/
theorem normTrilin_swap₂₃ (D : CubicJordanDatum J) (x y z : J) :
    D.normTrilin x y z = D.normTrilin x z y :=
  D.normTrilin_swap₂₃ x y z

/-- Derived symmetry between the first and third trilinear arguments. -/
theorem normTrilin_swap₁₃ (D : CubicJordanDatum J) (x y z : J) :
    D.normTrilin x y z = D.normTrilin z y x := by
  calc
    D.normTrilin x y z = D.normTrilin y x z := D.normTrilin_swap₁₂ x y z
    _ = D.normTrilin y z x := D.normTrilin_swap₂₃ y x z
    _ = D.normTrilin z y x := D.normTrilin_swap₁₂ y z x

/-- The quartic invariant is a polynomial in the `FreudenthalCharge` coordinates. -/
theorem quartic_invariant_poly (D : CubicJordanDatum J) (Q : FreudenthalCharge J) :
    quarticInvariant D Q =
      (Q.alpha * Q.beta - D.traceBilin Q.x Q.y) ^ 2 -
        4 * (Q.alpha * D.normCubic Q.x + Q.beta * D.normCubic Q.y -
              D.traceBilin (D.adjointQuad Q.x) (D.adjointQuad Q.y)) := by
  rfl

/-- The symplectic form on `FreudenthalCharge` is alternating. -/
theorem symplectic_alternating (D : CubicJordanDatum J) (Q : FreudenthalCharge J) :
    symplecticForm D Q Q = 0 :=
  symplectic_form_alternating D Q

/-- The symplectic form on `FreudenthalCharge` is skew-symmetric. -/
theorem symplectic_skew (D : CubicJordanDatum J) (Q₁ Q₂ : FreudenthalCharge J) :
    symplecticForm D Q₂ Q₁ = -symplecticForm D Q₁ Q₂ :=
  symplectic_form_skew D Q₁ Q₂

end InfoGeometry.Exceptional.FreudenthalCubicJordanBridge
