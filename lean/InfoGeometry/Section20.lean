import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Section12
import InfoGeometry.Section12Formalized

/-!
# Section 20: torsion bridge capstone

The upstream `section20.txt` currently repeats the torsion prose from Section 12.
This file repairs that duplicate source into a theorem-safe finite bridge between
the two existing torsion formalizations.

#### BUCKET 1: CLOSED FINITE THEOREMS
The Section 12 and Section 12 Formalized torsion coefficient definitions agree
definitionally.  Their coordinate Cartan coefficient conventions are reconciled:
Section 12 uses an explicitly reindexed coordinate connection form, while
Section 12 Formalized keeps the original coefficient order and recovers the same
torsion coefficient after swapping the two lower slots.  The quaternion torsion
definitions agree, and the finite shift commutator from Section 12 is the same
matrix as the generic commutator readout from Section 12 Formalized.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  All results are direct finite algebraic equalities or imported finite
theorems.

#### BUCKET 3: OPEN CLOSURE DEBT
No smooth manifold exterior calculus, Einstein-Cartan field equations,
axial-current coupling, propagating torsion, quantum anomaly theorem, or
emergent-spacetime theorem is claimed here.
-/

noncomputable section

namespace Section20

abbrev ConnectionCoeff := Fin 4 → Fin 4 → Fin 4 → ℂ
abbrev Quat := Section8.Quat
abbrev ShiftMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The two repaired torsion modules use the same finite coefficient formula. -/
theorem torsion_coefficient_definitions_agree
    (Gamma : ConnectionCoeff) (a b c : Fin 4) :
    Section12.torsionTensor Gamma a b c =
      Section12Formalized.torsionTensor Gamma a b c := by
  rfl

/--
The duplicate Section 20 torsion source has two compatible coordinate Cartan
readouts: Section 12 absorbs the coordinate index swap into
`coordinateConnectionForm`, while Section 12 Formalized keeps the original
coefficient order and swaps the lower slots at the readout.
-/
theorem coordinate_cartan_readouts_reconcile
    (Gamma : ConnectionCoeff) (a b c : Fin 4) :
    Section12.torsionTwoFormCoeff Section12.zeroConnection
        (Section12.coordinateConnectionForm Gamma) Section12.coordinateFrame a b c =
      Section12.torsionTensor Gamma a b c ∧
        Section12Formalized.torsionTwoFormCoeff Section12Formalized.zeroConnection
        Gamma Section12Formalized.coordinateFrame a c b =
      Section12Formalized.torsionTensor Gamma a b c := by
  refine ⟨?_, ?_⟩
  · exact Section12.torsionTwoFormCoeff_coordinate_eq_torsionTensor Gamma a b c
  · exact Section12Formalized.coordinate_basis_torsionTwoFormCoeff_swap_eq_torsionTensor
      Gamma a b c

/-- Both torsion modules use the same quaternion commutator covariant derivative. -/
theorem quaternion_torsion_definitions_agree (dq Omega q : Quat) :
    Section12.quaternionTorsion dq Omega q =
      Section12Formalized.quaternionTorsion dq Omega q := by
  rfl

/--
The finite noncommutative shift property is exactly an instance of the generic
commutator readout used by the formalized torsion corridor.
-/
theorem finite_shift_commutator_is_generic_readout :
    Section12Formalized.macroscopicCuntzTorsion
        Section12.finiteShiftL Section12.finiteShiftR =
      Section12.finiteShiftCommutator := by
  rfl

/-- The generic commutator readout is nonzero on the finite two-site shifts. -/
theorem finite_shift_generic_readout_ne_zero :
    Section12Formalized.macroscopicCuntzTorsion
        Section12.finiteShiftL Section12.finiteShiftR ≠ (0 : ShiftMat) := by
  rw [finite_shift_commutator_is_generic_readout]
  exact Section12.finiteShiftCommutator_ne_zero

theorem section20_capstone :
    (∀ Gamma : ConnectionCoeff, ∀ a b c : Fin 4,
      Section12.torsionTensor Gamma a b c =
        Section12Formalized.torsionTensor Gamma a b c) ∧
    (∀ Gamma : ConnectionCoeff, ∀ a b c : Fin 4,
      Section12.torsionTwoFormCoeff Section12.zeroConnection
          (Section12.coordinateConnectionForm Gamma) Section12.coordinateFrame a b c =
        Section12.torsionTensor Gamma a b c ∧
      Section12Formalized.torsionTwoFormCoeff Section12Formalized.zeroConnection
          Gamma Section12Formalized.coordinateFrame a c b =
        Section12Formalized.torsionTensor Gamma a b c) ∧
    (∀ dq Omega q : Quat,
      Section12.quaternionTorsion dq Omega q =
        Section12Formalized.quaternionTorsion dq Omega q) ∧
        Section12Formalized.macroscopicCuntzTorsion
        Section12.finiteShiftL Section12.finiteShiftR ≠ (0 : ShiftMat) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact torsion_coefficient_definitions_agree
  · exact coordinate_cartan_readouts_reconcile
  · exact quaternion_torsion_definitions_agree
  · exact finite_shift_generic_readout_ne_zero

end Section20
