import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

namespace InfoGeometry.Canonical

/--
Analog Gravity Archetypes representing the topological phases of the system.
-/
inductive AnalogGravityArchetype
  | zornBdGHamiltonianChiral
  | chiralZitterbewegungBridge
  | madelungNavierStokesClosure
  | souriauLieThermoKKTBridge
  deriving Repr, DecidableEq, Fintype

open AnalogGravityArchetype

def AnalogGravityArchetype.toNat : AnalogGravityArchetype → Nat
  | zornBdGHamiltonianChiral => 0
  | chiralZitterbewegungBridge => 1
  | madelungNavierStokesClosure => 2
  | souriauLieThermoKKTBridge => 3

instance : LE AnalogGravityArchetype where
  le a b := a.toNat ≤ b.toNat

instance (a b : AnalogGravityArchetype) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance : PartialOrder AnalogGravityArchetype where
  le := (· ≤ ·)
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

end InfoGeometry.Canonical
