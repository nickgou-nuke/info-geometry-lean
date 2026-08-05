import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import InfoGeometry.OperatorAlgebra.DualSplitOctonionRootKleinBraidBridge
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.BrillouinKleinExceptionalTopology

/-!
# Finite Klein-Brillouin Berry-connection shadow

This module records the discrete algebraic part of the Klein-Brillouin gauge
connection discussion.  It keeps only finite matrix and parity identities:

* the cross-cap monodromy is the block swap `M_y` from the dual split-octonion
  root/Klein/braid bridge;
* for a constant monodromy, derivative correction terms are zero by definition;
* the `x` connection component picks up the orientation sign, while the `y`
  component does not;
* the phase-line readout is a parity invariant in `ZMod 2`;
* `G₂` and `E₇` are represented here only by Cartan/dimension ledgers.

No smooth Berry bundle, analytic Wilson loop, band-Hamiltonian theorem,
continuum curvature theorem, or high-energy duality theorem is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.KleinBerryConnectionFinite

open Matrix
open InfoGeometry.OperatorAlgebra.DualSplitOctonionRootKleinBraidBridge

abbrev Conn8Z := Matrix (Fin 8) (Fin 8) ℤ

/-- Finite pair of connection components on the KBZ chart. -/
@[ext]
structure FiniteKBZConnection where
  Ax : Conn8Z
  Ay : Conn8Z
  deriving DecidableEq, Repr

/-- Constant cross-cap monodromy; derivative correction vanishes in this finite model. -/
def monodromyDerivativeCorrection : Conn8Z := 0

/-- Orientation-reversing `x`-component transform. -/
def transformAx (A : Conn8Z) : Conn8Z :=
  -(My * A * My)

/-- Orientation-preserving `y`-component transform. -/
def transformAy (A : Conn8Z) : Conn8Z :=
  My * A * My

/-- Finite KBZ connection transform. -/
def transformConnection (C : FiniteKBZConnection) : FiniteKBZConnection where
  Ax := transformAx C.Ax + monodromyDerivativeCorrection
  Ay := transformAy C.Ay + monodromyDerivativeCorrection

/-- The constant-monodromy derivative term is zero. -/
theorem monodromyDerivativeCorrection_zero :
    monodromyDerivativeCorrection = (0 : Conn8Z) := by
  rfl

/-- Readback of the finite `x`-component glide rule. -/
theorem transformConnection_Ax (C : FiniteKBZConnection) :
    (transformConnection C).Ax = -(My * C.Ax * My) := by
  simp [transformConnection, transformAx, monodromyDerivativeCorrection]

/-- Readback of the finite `y`-component glide rule. -/
theorem transformConnection_Ay (C : FiniteKBZConnection) :
    (transformConnection C).Ay = My * C.Ay * My := by
  simp [transformConnection, transformAy, monodromyDerivativeCorrection]

/-- The zero connection is fixed by the finite KBZ transform. -/
theorem transformConnection_zero :
    transformConnection ⟨0, 0⟩ = ⟨0, 0⟩ := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

/-- Integer crossing count reduced to the finite `Z₂` phase invariant. -/
def phaseParity (crossings : ℤ) : ZMod 2 :=
  crossings

/-- A one-crossing phase line is the nontrivial `Z₂` class. -/
theorem phaseParity_one :
    phaseParity 1 = (1 : ZMod 2) := by
  rfl

/-- Adding two crossings does not change the `Z₂` phase class. -/
theorem phaseParity_add_two (n : ℤ) :
    phaseParity (n + 2) = phaseParity n := by
  change ((n + 2 : ℤ) : ZMod 2) = (n : ZMod 2)
  rw [Int.cast_add]
  change (n : ZMod 2) + (2 : ZMod 2) = (n : ZMod 2)
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]
  simp

/-- The repository's integer Klein invariant gives zero for an antisymmetric boundary pair. -/
theorem antisymmetric_boundary_klein_invariant_zero (theta : ℤ) :
    InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant theta (-theta) = 0 := by
  simp [InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant]

/-- The additive Klein boundary owner reduces the zero path to even charge. -/
theorem zero_path_klein_boundary_even :
    InfoGeometry.Topology.BrillouinKlein.klein_bottle_boundary ℤ 0 0 = 2 * (0 : ℤ) := by
  rfl

/-! ## Exact exceptional Cartan/dimension ledgers -/

/-- Cartan matrix for the `G₂` root system in the convention used by the braid shadow. -/
def g2Cartan : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -3;
     -1, 2]

/-- Dimension ledger for the split real `G₂` Lie algebra. -/
def g2Dimension : Nat := 14

/-- Dimension ledger for the complex/split `E₇` Lie algebra. -/
def e7Dimension : Nat := 133

/-- Dimension ledger for `SU(8)`. -/
def su8Dimension : Nat := 63

/-- Symmetric-space scalar-count ledger `133 - 63 = 70`. -/
def e7Su8ScalarLedger : Nat := e7Dimension - su8Dimension

/-- The finite `G₂` Cartan entries include the long/short-root coefficient `-3`. -/
theorem g2Cartan_entries :
    g2Cartan 0 0 = 2 ∧ g2Cartan 0 1 = -3 ∧
      g2Cartan 1 0 = -1 ∧ g2Cartan 1 1 = 2 := by
  decide

/-- Exact dimension ledger for the `G₂` and `E₇/SU(8)` bookkeeping layer. -/
theorem exceptional_dimension_ledger :
    g2Dimension = 14 ∧ e7Dimension = 133 ∧ su8Dimension = 63 ∧
      e7Su8ScalarLedger = 70 := by
  decide

end InfoGeometry.OperatorAlgebra.KleinBerryConnectionFinite
