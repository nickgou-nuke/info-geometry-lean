import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.OperatorAlgebra

/-- Dual Connections on Each Sheet.
    Provides connections for an operator algebra A. -/
structure SheetConnection (A : Type*) where
  Γ : A → A → A
  α : ℝ

/-- Torsion of the connection. T(u,v) = Γ(u,v) - Γ(v,u) - [u,v] -/
def SheetConnection.torsion {A : Type*} [Ring A] (conn : SheetConnection A) (u v : A) : A :=
  conn.Γ u v - conn.Γ v u - (u * v - v * u)

end InfoGeometry.OperatorAlgebra
