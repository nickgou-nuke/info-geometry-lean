import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

namespace InfoGeometry.Canonical

/--
Analog Gravity Archetypes representing the topological phases of the system.
-/
inductive AnalogGravityArchetype
  | zornBdGHamiltonianChiral
  | chiralZitterbewegungBridge
  | madelungNavierStokesClosure
  | souriauLieThermoKKTBridge
  deriving Repr, DecidableEq

open AnalogGravityArchetype

def analogGravityArchetypeEquiv : AnalogGravityArchetype ≃ Fin 4 where
  toFun
    | .zornBdGHamiltonianChiral => 0
    | .chiralZitterbewegungBridge => 1
    | .madelungNavierStokesClosure => 2
    | .souriauLieThermoKKTBridge => 3
  invFun
    | 0 => .zornBdGHamiltonianChiral
    | 1 => .chiralZitterbewegungBridge
    | 2 => .madelungNavierStokesClosure
    | 3 => .souriauLieThermoKKTBridge
  left_inv a := by cases a <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype AnalogGravityArchetype :=
  Fintype.ofEquiv (Fin 4) analogGravityArchetypeEquiv.symm

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
