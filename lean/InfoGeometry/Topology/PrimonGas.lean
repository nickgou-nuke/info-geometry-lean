import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite primon-gas parameter packet

This module records a small state structure and a predicate equal to its
`E_0 > T` field.  It does not construct a Riemann gas, prove a zeta partition
function theorem, or prove any Riemann-hypothesis statement.
-/

namespace InfoGeometry.Topology.PrimonGas

/-- The structure defining a generic Primon Gas state. -/
structure PrimonGasState where
  /-- The base energy scaling factor. -/
  E_0 : ℝ
  /-- The temperature of the system. -/
  T : ℝ
  /-- Supplied strict parameter inequality. -/
  below_hagedorn : E_0 > T

/-- The local validity predicate used by this finite packet. -/
def primonGasParameterValid (state : PrimonGasState) : Prop :=
  state.E_0 > state.T

/-- The local validity predicate is definitionally the supplied inequality. -/
theorem primonGasParameterValid_iff (state : PrimonGasState) :
    primonGasParameterValid state ↔ state.E_0 > state.T := by
  rfl

end InfoGeometry.Topology.PrimonGas
