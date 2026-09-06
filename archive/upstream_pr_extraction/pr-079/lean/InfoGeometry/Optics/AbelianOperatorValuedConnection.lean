import InfoGeometry.Optics.OperatorValuedConnection

noncomputable section

/-!
# Abelian reduction of operator-valued curvature

The generic connection owner defines `F = derivative + Ω ∧ Ω`.  This adapter
records the precise Abelian specialization: when the connection values
commute pairwise, the wedge-square term vanishes and curvature is exactly the
stored exterior derivative contribution.
-/

namespace InfoGeometry.Optics.OperatorValuedConnection

open InfoGeometry.Geometry.BilingualAnalyticity

variable {Point Tangent Value : Type*} [Ring Value]

/-- Pairwise commutativity of the values of a connection one-form. -/
def IsAbelianForm
    (ω : OperatorOneForm Point Tangent Value) : Prop :=
  ∀ p X Y, ω p X * ω p Y = ω p Y * ω p X

theorem wedgeSquare_eq_zero_of_abelian
    (ω : OperatorOneForm Point Tangent Value)
    (hAbelian : IsAbelianForm ω) (p : Point) (X Y : Tangent) :
    wedgeSquare ω p X Y = 0 := by
  unfold wedgeSquare
  rw [hAbelian p X Y]
  simp

theorem curvature_eq_derivative_of_abelian
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (hAbelian : IsAbelianForm C.form) (p : Point) (X Y : Tangent) :
    curvature C p X Y = C.derivative p X Y := by
  unfold curvature
  rw [wedgeSquare_eq_zero_of_abelian C.form hAbelian p X Y]
  simp

end InfoGeometry.Optics.OperatorValuedConnection
