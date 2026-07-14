import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite Brillouin-Klein Berry connection shadow

Lean twin:
`tools/sympy/klein_berry_connection_finite.py`.

This module mirrors only the finite, theorem-safe shadow of the pasted KBZ
Berry-connection discussion:

#### BUCKET 1: CLOSED FINITE THEOREMS

* an explicit eight-slot cross-cap block swap is involutive;
* a zero derivative correction leaves the finite connection transform as the
  conjugation/sign formula;
* the integer `Z₂` phase readout is insensitive to orientation reversal and
  to adding two crossings;
* the finite Cartan/dimension readouts used by the Python verifier are
  arithmetically consistent.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not formalize analytic Berry bundles, differentiable Bloch
wavefunctions, smooth nonabelian connections, Wilson-loop spectra,
Hamiltonian band topology, AdS/CFT, supersymmetry, supergravity, a quantum
`G₂` `R`-matrix, or a Yang-Baxter theorem.
-/

namespace BrillouinKleinBerryConnectionFinite

/-- Eight-slot cross-cap block swap: the first four slots exchange with the last four. -/
def crossCapIndex : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3

/-- The finite cross-cap index swap is an involution. -/
theorem crossCapIndex_involutive : Function.Involutive crossCapIndex := by
  intro i
  fin_cases i <;> rfl

/-- Matrix-carrier type for the finite eight-band shadow. -/
abbrev Mat8 := Matrix (Fin 8) (Fin 8) ℤ

/-- Finite `A_x` transform under a constant cross-cap monodromy. -/
def transformAx (M A dM : Mat8) : Mat8 :=
  -M * A * M + dM

/-- Finite `A_y` transform under a constant cross-cap monodromy. -/
def transformAy (M A dM : Mat8) : Mat8 :=
  M * A * M + dM

/-- With zero derivative correction, the `A_x` transform is just signed conjugation. -/
theorem transformAx_zero_derivative (M A : Mat8) :
    transformAx M A 0 = -M * A * M := by
  simp [transformAx]

/-- With zero derivative correction, the `A_y` transform is just conjugation. -/
theorem transformAy_zero_derivative (M A : Mat8) :
    transformAy M A 0 = M * A * M := by
  simp [transformAy]

/-- Integer crossing parity used by the finite phase shadow. -/
def phaseParity (crossings : ℤ) : ℤ :=
  crossings % 2

/-- Orientation reversal cancels in the existing Brillouin-Klein `Z₂` readout. -/
theorem klein_z2_orientation_reversal_cancel (theta : ℤ) :
    InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant theta (-theta) = 0 := by
  simp [InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant]

/-- Crossing parity is stable under adding two crossings. -/
theorem phaseParity_add_two (n : ℤ) :
    phaseParity (n + 2) = phaseParity n := by
  simp [phaseParity]

/-- The odd crossing readout is the nontrivial `Z₂` class. -/
theorem phaseParity_one :
    phaseParity 1 = 1 := by
  rfl

/-- Finite Cartan entry ledger for type `G₂`. -/
def g2Cartan00 : ℤ := 2

/-- Finite Cartan entry ledger for type `G₂`. -/
def g2Cartan01 : ℤ := -3

/-- Finite Cartan entry ledger for type `G₂`. -/
def g2Cartan10 : ℤ := -1

/-- Finite Cartan entry ledger for type `G₂`. -/
def g2Cartan11 : ℤ := 2

/-- Dimension of the split/complex `G₂` Lie algebra readout. -/
def g2LieDimension : Nat := 14

/-- Dimension of the split/complex `E₇` Lie algebra readout. -/
def e7LieDimension : Nat := 133

/-- Dimension of `SU(8)` used only for the arithmetic scalar-coset ledger. -/
def su8Dimension : Nat := 63

/-- Scalar-coset dimension ledger `133 - 63 = 70`. -/
def e7OverSu8ScalarDimension : Nat := 70

/-- The finite `G₂` Cartan matrix determinant ledger. -/
theorem g2_cartan_det_ledger :
    g2Cartan00 * g2Cartan11 - g2Cartan01 * g2Cartan10 = 1 := by
  norm_num [g2Cartan00, g2Cartan01, g2Cartan10, g2Cartan11]

/-- The finite exceptional dimension ledger used by the runtime verifier. -/
theorem exceptional_dimension_ledger :
    e7LieDimension - su8Dimension = e7OverSu8ScalarDimension ∧
      g2LieDimension = 14 := by
  norm_num [e7LieDimension, su8Dimension, e7OverSu8ScalarDimension, g2LieDimension]

/-- Closed finite packet for the KBZ Berry-connection shadow. -/
theorem brillouinKleinBerryConnectionFinite_packet :
    Function.Involutive crossCapIndex ∧
      (∀ M A : Mat8, transformAx M A 0 = -M * A * M) ∧
      (∀ M A : Mat8, transformAy M A 0 = M * A * M) ∧
      (∀ theta : ℤ,
        InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant theta (-theta) = 0) ∧
      (∀ n : ℤ, phaseParity (n + 2) = phaseParity n) ∧
      phaseParity 1 = 1 ∧
      g2Cartan00 * g2Cartan11 - g2Cartan01 * g2Cartan10 = 1 ∧
      e7LieDimension - su8Dimension = e7OverSu8ScalarDimension ∧
      g2LieDimension = 14 := by
  exact ⟨crossCapIndex_involutive, transformAx_zero_derivative, transformAy_zero_derivative,
    klein_z2_orientation_reversal_cancel, phaseParity_add_two, phaseParity_one,
    g2_cartan_det_ledger, exceptional_dimension_ledger.1, exceptional_dimension_ledger.2⟩

end BrillouinKleinBerryConnectionFinite
