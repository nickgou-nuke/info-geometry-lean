import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Spin transport of operator-valued `Cl(5,5)` connections

The value algebra is the full noncommutative Clifford algebra `Cl55`.  Spin
transport is therefore an inner `RingEquiv`, and the curvature statement is
proved by transporting addition, subtraction, and multiplication through that
equivalence.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent : Type*}

abbrev Cl55Connection (Point Tangent : Type*) :=
  Connection (Point := Point) (Tangent := Tangent) (Value := Cl55)

noncomputable def spinTransportedConnection
    (g : Spin55) (C : Cl55Connection Point Tangent) :
    Cl55Connection Point Tangent where
  form p X := spinCliffordRingEquiv g (C.form p X)
  derivative p X Y := spinCliffordRingEquiv g (C.derivative p X Y)
  derivative_swap p X Y := by
    rw [C.derivative_swap]
    exact (spinCliffordRingEquiv g).map_neg _
  derivative_same p X := by
    rw [C.derivative_same]
    exact (spinCliffordRingEquiv g).map_zero

theorem spinTransportedConnection_curvature
    (g : Spin55) (C : Cl55Connection Point Tangent)
    (p : Point) (X Y : Tangent) :
    curvature (spinTransportedConnection g C) p X Y =
      spinCliffordRingEquiv g (curvature C p X Y) := by
  simp only [curvature, wedgeSquare, spinTransportedConnection,
    map_add, map_sub, map_mul]

theorem spinTransportedConnection_flat_iff
    (g : Spin55) (C : Cl55Connection Point Tangent) :
    IsFlat (spinTransportedConnection g C) ↔ IsFlat C := by
  constructor
  · intro h p X Y
    apply (spinCliffordRingEquiv g).injective
    rw [← spinTransportedConnection_curvature g C p X Y]
    calc
      curvature (spinTransportedConnection g C) p X Y = 0 := h p X Y
      _ = (spinCliffordRingEquiv g) 0 :=
        ((spinCliffordRingEquiv g).map_zero).symm
  · intro h p X Y
    rw [spinTransportedConnection_curvature]
    rw [h p X Y]
    exact (spinCliffordRingEquiv g).map_zero

end InfoGeometry.Clifford.Clifford55
