import InfoGeometry.Clifford.Cl55SpinOperatorConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55CAROperatorLift

/-!
# Faithful operator realization of `Cl(5,5)` connections

Left multiplication embeds the full Clifford algebra into its endomorphism
algebra.  The embedding is used here on the complete connection and its
curvature, retaining the noncommutative product.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent : Type*}

abbrev Cl55OperatorConnection (Point Tangent : Type*) :=
  Connection (Point := Point) (Tangent := Tangent) (Value := Cl55Operator)

def leftActionConnection55
    (C : Cl55Connection Point Tangent) :
    Cl55OperatorConnection Point Tangent where
  form p X := leftAction55 (C.form p X)
  derivative p X Y := leftAction55 (C.derivative p X Y)
  derivative_swap p X Y := by
    rw [C.derivative_swap]
    exact leftAction55_neg _
  derivative_same p X := by
    rw [C.derivative_same]
    exact leftAction55_zero

theorem leftAction55_injective :
    Function.Injective leftAction55 := by
  intro a b h
  have h1 := congrArg (fun T : Cl55Operator => T (1 : Cl55)) h
  simpa [leftAction55] using h1

theorem leftActionConnection55_curvature
    (C : Cl55Connection Point Tangent) (p : Point) (X Y : Tangent) :
    curvature (leftActionConnection55 C) p X Y =
      leftAction55 (curvature C p X Y) := by
  change leftAction55 (C.derivative p X Y) +
      (leftAction55 (C.form p X) * leftAction55 (C.form p Y) -
        leftAction55 (C.form p Y) * leftAction55 (C.form p X)) =
    leftAction55 (C.derivative p X Y +
      (C.form p X * C.form p Y - C.form p Y * C.form p X))
  rw [← leftAction55_mul, ← leftAction55_mul, ← leftAction55_sub,
    ← leftAction55_add]

theorem leftActionConnection55_flat_iff
    (C : Cl55Connection Point Tangent) :
    IsFlat (leftActionConnection55 C) ↔ IsFlat C := by
  constructor
  · intro h p X Y
    have hc : leftAction55 (curvature C p X Y) =
        leftAction55 (0 : Cl55) := by
      calc
        leftAction55 (curvature C p X Y) =
            curvature (leftActionConnection55 C) p X Y :=
              (leftActionConnection55_curvature C p X Y).symm
        _ = 0 := h p X Y
        _ = leftAction55 (0 : Cl55) := leftAction55_zero.symm
    exact leftAction55_injective hc
  · intro h p X Y
    rw [leftActionConnection55_curvature, h p X Y]
    exact leftAction55_zero

end InfoGeometry.Clifford.Clifford55
