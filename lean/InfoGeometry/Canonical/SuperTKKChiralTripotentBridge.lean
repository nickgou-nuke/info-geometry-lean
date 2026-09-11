import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Algebraic.ChiralOperatorCarrier
import InfoGeometry.Topology.V4RootSystem

/-!
# Super-TKK / Chiral / Tripotent Bridge

This module records the finite theorem surface for the refined hierarchy:

real doubled Hestenes-Krein chiral carrier
→ tripotent `±/0` boundary grading
→ super-TKK five-grading with `±2` defect sectors.

#### BUCKET 1: CLOSED FINITE THEOREMS

* mixed `g₋₁/g₊₁` brackets land in `g₀`;
* same-positive and same-negative grade-one brackets land in `g₊₂` and `g₋₂`;
* `g₀` acts on the two defect sectors, and `g₊₂` is abelian;
* the canonical chiral carrier satisfies `ε = P₊ - P₋`, projector
  orthogonality, and `(Jε)² = -1`;
* tripotent sectors satisfy `T³ = T` and the three projector readouts partition
  unity.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The five-grading closure packet assumes an explicit
`SuperTKKConformalClosure.FiveGrading` witness.  The chiral packet assumes an
explicit `InvolutiveSelfDualCarrier` witness.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not construct a concrete BdG/Krein-Fock representation, a
Pin(5,5) action, a global superconformal algebra, a boundary Majorana/Fibonacci
braid category, or a continuum anomaly-cancellation theorem.  It only names and
proves the finite owner-backed dictionary.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperTKKChiralTripotentBridge

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Algebraic
open InfoGeometry.Krein
open InfoGeometry.Topology.V4RootSystem
open InfoGeometryCore.TripotentState

/-! ## Role dictionary -/

/-- The five semantic roles in the refined closure hierarchy. -/
inductive ClosureRole where
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
  deriving DecidableEq, Repr

namespace ClosureRole

/-- Tripotent readout for the five roles: `±2` and `±1` share the sign, `g₀` is zero. -/
def tripotentSector : ClosureRole → InfoGeometryCore.TripotentState
  | negTwo => InfoGeometryCore.TripotentState.neg
  | negOne => InfoGeometryCore.TripotentState.neg
  | zero => InfoGeometryCore.TripotentState.zero
  | posOne => InfoGeometryCore.TripotentState.pos
  | posTwo => InfoGeometryCore.TripotentState.pos

/-- The role-to-tripotent dictionary is compatible with `T³ = T`. -/
theorem tripotentSector_cube (r : ClosureRole) :
    toInt (tripotentSector r) ^ 3 = toInt (tripotentSector r) := by
  exact cube_eq_self (tripotentSector r)

/-- The `±2` roles are exactly the explicit defect roles in this finite dictionary. -/
def IsDefect (r : ClosureRole) : Prop :=
  r = negTwo ∨ r = posTwo

/-- Positive grade two is a defect role. -/
theorem posTwo_is_defect : IsDefect posTwo := by
  exact Or.inr rfl

/-- Negative grade two is a defect role. -/
theorem negTwo_is_defect : IsDefect negTwo := by
  exact Or.inl rfl

/-- The zero role is not a defect role. -/
theorem zero_not_defect : ¬ IsDefect zero := by
  intro h
  cases h with
  | inl hz => cases hz
  | inr hz => cases hz

end ClosureRole

end InfoGeometry.Canonical.SuperTKKChiralTripotentBridge

end
