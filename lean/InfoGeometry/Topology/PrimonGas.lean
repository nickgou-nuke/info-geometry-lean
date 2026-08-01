import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite primon-gas parameter packet

This module records a small state structure and a predicate equal to its
`E_0 > T` field.  It does not construct a Riemann gas, prove a zeta partition
function theorem, or prove any Riemann-hypothesis statement.
-/

namespace InfoGeometry.Topology.PrimonGas

/- The finite state is a pair of real parameters satisfying the Hagedorn bound. -/
def PrimonGasState := {p : ℝ × ℝ // p.1 > p.2}

namespace PrimonGasState

def E_0 (state : PrimonGasState) : ℝ := state.1.1
def T (state : PrimonGasState) : ℝ := state.1.2

theorem below_hagedorn (state : PrimonGasState) : state.E_0 > state.T :=
  state.2

end PrimonGasState

/-- The local validity predicate used by this finite packet. -/
def primonGasParameterValid (state : PrimonGasState) : Prop :=
  state.E_0 > state.T

/-- The local validity predicate is definitionally the supplied inequality. -/
theorem primonGasParameterValid_iff (state : PrimonGasState) :
    primonGasParameterValid state ↔ state.E_0 > state.T := by
  rfl

end InfoGeometry.Topology.PrimonGas
