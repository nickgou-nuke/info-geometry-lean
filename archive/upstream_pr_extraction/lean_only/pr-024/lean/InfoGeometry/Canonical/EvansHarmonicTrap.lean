import Mathlib
import InfoGeometry.GrandUnification.HodgeTrifactorBridge

/-!
# Evans 1D Lattice Harmonic Trap

This module formalizes the finite three-symbol driven lattice rule set used as
an algebraic analogy for exact/coexact/harmonic sector blocking.

The closed layer is purely local and combinatorial:
* `exact, harmonic ↦ harmonic, exact`;
* `harmonic, coexact ↦ coexact, harmonic`;
* `exact, coexact ↦ coexact, exact`;
* all other adjacent pairs are fixed.

No statistical-mechanics thermodynamic limit, spontaneous-symmetry-breaking
theorem, KMS phase transition, CFT model, zeta-zero theorem, or RH consequence
is asserted here.

#### BUCKET 1: CLOSED FINITE THEOREMS
The local transition rules, the two blocked trap-boundary pairs, and the
left/right update invariance of the finite triple
`(coexact, harmonic, exact)`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
Any thermodynamic-limit theorem, connection to the Evans-Foster-Godreche-Mukamel
model beyond this local rule table, KMS/BEC interpretation, or zeta/RH
interpretation.
-/

namespace InfoGeometry.Canonical.EvansHarmonicTrap

open InfoGeometry.GrandUnification.HodgeTrifactorBridge

/-! ## Three finite charge labels -/

/-- Three local lattice labels: exact current, coexact current, and harmonic hole. -/
inductive LatticeCharge
  | exact
  | coexact
  | harmonic
  deriving DecidableEq, Repr

/-- Dictionary from the lattice labels to the finite Hodge/trifactor labels. -/
def toHodgeSector : LatticeCharge → HodgeSector
  | LatticeCharge.exact => HodgeSector.exact
  | LatticeCharge.coexact => HodgeSector.coexact
  | LatticeCharge.harmonic => HodgeSector.harmonic

theorem toHodgeSector_exact :
    toHodgeSector LatticeCharge.exact = HodgeSector.exact := rfl

theorem toHodgeSector_coexact :
    toHodgeSector LatticeCharge.coexact = HodgeSector.coexact := rfl

theorem toHodgeSector_harmonic :
    toHodgeSector LatticeCharge.harmonic = HodgeSector.harmonic := rfl

/-! ## Local Evans-style transition table -/

/-- Local deterministic adjacent-pair transition. -/
def local_transition : LatticeCharge × LatticeCharge → LatticeCharge × LatticeCharge
  | (LatticeCharge.exact, LatticeCharge.harmonic) =>
      (LatticeCharge.harmonic, LatticeCharge.exact)
  | (LatticeCharge.harmonic, LatticeCharge.coexact) =>
      (LatticeCharge.coexact, LatticeCharge.harmonic)
  | (LatticeCharge.exact, LatticeCharge.coexact) =>
      (LatticeCharge.coexact, LatticeCharge.exact)
  | pair => pair

/-- An exact current moves right through a harmonic site. -/
theorem exact_harmonic_moves_right :
    local_transition (LatticeCharge.exact, LatticeCharge.harmonic) =
      (LatticeCharge.harmonic, LatticeCharge.exact) := rfl

/-- A coexact current moves left through a harmonic site. -/
theorem harmonic_coexact_moves_left :
    local_transition (LatticeCharge.harmonic, LatticeCharge.coexact) =
      (LatticeCharge.coexact, LatticeCharge.harmonic) := rfl

/-- Oppositely oriented active currents swap. -/
theorem exact_coexact_swap :
    local_transition (LatticeCharge.exact, LatticeCharge.coexact) =
      (LatticeCharge.coexact, LatticeCharge.exact) := rfl

/--
Left boundary of the harmonic trap is fixed: a coexact current immediately to
the left of a harmonic block cannot cross by the local rule.
-/
theorem harmonic_trap_invariant_left :
    local_transition (LatticeCharge.coexact, LatticeCharge.harmonic) =
      (LatticeCharge.coexact, LatticeCharge.harmonic) := rfl

/--
Right boundary of the harmonic trap is fixed: an exact current immediately to
the right of a harmonic block cannot cross by the local rule.
-/
theorem harmonic_trap_invariant_right :
    local_transition (LatticeCharge.harmonic, LatticeCharge.exact) =
      (LatticeCharge.harmonic, LatticeCharge.exact) := rfl

/-! ## Three-site trap readout -/

/-- A three-site local window. -/
structure LatticeTriple where
  left : LatticeCharge
  center : LatticeCharge
  right : LatticeCharge
  deriving DecidableEq, Repr

/-- The finite harmonic trap window: coexact current, harmonic site, exact current. -/
def harmonicTrap : LatticeTriple where
  left := LatticeCharge.coexact
  center := LatticeCharge.harmonic
  right := LatticeCharge.exact

/-- Apply the local transition to the left adjacent pair of a triple. -/
def updateLeft (c : LatticeTriple) : LatticeTriple :=
  let pair := local_transition (c.left, c.center)
  { left := pair.1, center := pair.2, right := c.right }

/-- Apply the local transition to the right adjacent pair of a triple. -/
def updateRight (c : LatticeTriple) : LatticeTriple :=
  let pair := local_transition (c.center, c.right)
  { left := c.left, center := pair.1, right := pair.2 }

/-- Updating the left boundary of the harmonic trap leaves the window fixed. -/
theorem harmonic_trap_updateLeft :
    updateLeft harmonicTrap = harmonicTrap := rfl

/-- Updating the right boundary of the harmonic trap leaves the window fixed. -/
theorem harmonic_trap_updateRight :
    updateRight harmonicTrap = harmonicTrap := rfl

/-- Both adjacent updates leave the finite harmonic trap fixed. -/
theorem harmonic_trap_pairwise_invariant :
    updateLeft harmonicTrap = harmonicTrap ∧
      updateRight harmonicTrap = harmonicTrap := by
  exact ⟨harmonic_trap_updateLeft, harmonic_trap_updateRight⟩

end InfoGeometry.Canonical.EvansHarmonicTrap
