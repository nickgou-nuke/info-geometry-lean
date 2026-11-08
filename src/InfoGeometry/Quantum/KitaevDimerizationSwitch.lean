/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Quantum.KitaevPauliBraiding
import InfoGeometry.Meta.ArchetypePipeline

/-!
# Concrete matrix archetype for the Majorana dimerization switch

This owner compares the two bond pairings in the repository's explicit
four-generator `4 × 4` complex matrix Clifford representation. It proves a
boundary-commutator distinction at these endpoints; it does not identify that
distinction with a full parameter-cycle parity pump or a spectral-gap theorem.
-/

noncomputable section

namespace InfoGeometry.Quantum.KitaevDimerizationSwitch

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.MetaCompiler

private def majoranaCommutator (X Y : Pauli4) : Pauli4 := X * Y - Y * X

/-- The inter-cell bond on the existing four-Majorana matrix representation. -/
def pauliInterCellHamiltonian : Pauli4 :=
  pauliMajorana 1 * pauliMajorana 2

/-- The represented inter-cell Majorana pair squares to `-1`, confirming that
the Kitaev bond is not a square-zero edge of a Peirce/Zorn path. -/
theorem pauliInterCell_bond_square :
    pauliInterCellHamiltonian * pauliInterCellHamiltonian = -1 := by
  simpa [pauliInterCellHamiltonian, pauliMajoranaOperators, pauliMajorana] using
    majorana_bond_square pauliMajoranaOperators 1 2 (by decide)

/-- The opposite, intra-cell pairing on the same four-mode matrix carrier. -/
def pauliIntraCellHamiltonian : Pauli4 :=
  intraCellDimerHamiltonian pauliMajoranaOperators

/-- The ordered product of the four Majorana generators on this Fock-space
matrix carrier. -/
def pauliFermionParity : Pauli4 :=
  pauliMajorana 0 * pauliMajorana 1 * pauliMajorana 2 * pauliMajorana 3

/-- The inter-cell dimer Hamiltonian preserves the represented fermion parity. -/
theorem interCell_preserves_fermion_parity :
    majoranaCommutator pauliFermionParity pauliInterCellHamiltonian = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaCommutator, pauliFermionParity, pauliInterCellHamiltonian,
      pauliMajorana, pauliMajorana0, pauliMajorana1, pauliMajorana2,
      pauliMajorana3, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- The intra-cell dimer Hamiltonian also preserves the represented fermion
parity. -/
theorem intraCell_preserves_fermion_parity :
    majoranaCommutator pauliFermionParity pauliIntraCellHamiltonian = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [majoranaCommutator, pauliFermionParity, pauliIntraCellHamiltonian,
      intraCellDimerHamiltonian, pauliMajoranaOperators, pauliMajorana,
      pauliMajorana0, pauliMajorana1, pauliMajorana2, pauliMajorana3,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- The inter-cell pairing leaves the left boundary Majorana conserved. -/
theorem interCell_boundary_commutator_zero :
    majoranaCommutator pauliInterCellHamiltonian (pauliMajorana 0) = 0 := by
  have h := gamma_comm_product_of_avoids
    pauliMajoranaOperators.toMajoranaOperators
    (⟨0, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)
    (⟨2, by decide⟩ : Fin 4) (by decide) (by decide)
  change pauliMajorana 0 * (pauliMajorana 1 * pauliMajorana 2) =
    (pauliMajorana 1 * pauliMajorana 2) * pauliMajorana 0 at h
  change (pauliMajorana 1 * pauliMajorana 2) * pauliMajorana 0 -
    pauliMajorana 0 * (pauliMajorana 1 * pauliMajorana 2) = 0
  exact sub_eq_zero.mpr h.symm

theorem pauliMajorana1_add_self_ne_zero :
    pauliMajorana 1 + pauliMajorana 1 ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Pauli4 => M 2 0) h
  norm_num [pauliMajorana, pauliMajorana1] at hentry

/-- The intra-cell pairing has the exact boundary commutator supplied by the
generic Clifford owner. -/
theorem intraCell_boundary_commutator_exact :
    majoranaCommutator pauliIntraCellHamiltonian (pauliMajorana 0) =
      -(pauliMajorana 1 + pauliMajorana 1) := by
  simpa [majoranaCommutator, InfoGeometry.Quantum.KitaevChain.commutator,
      pauliIntraCellHamiltonian, pauliMajoranaOperators] using
    intraCellDimer_left_boundary_commutator pauliMajoranaOperators

/-- In this concrete matrix representation the intra-cell boundary
commutator is genuinely nonzero. -/
theorem intraCell_boundary_commutator_ne_zero :
    majoranaCommutator pauliIntraCellHamiltonian (pauliMajorana 0) ≠ 0 := by
  rw [intraCell_boundary_commutator_exact]
  intro h
  exact pauliMajorana1_add_self_ne_zero (neg_eq_zero.mp h)

/-- The concrete dimerization switch changes the boundary commutator from
zero to a nonzero matrix operator. -/
theorem pauli_dimerization_switch_operator_laws :
    majoranaCommutator pauliInterCellHamiltonian (pauliMajorana 0) = 0 ∧
    majoranaCommutator pauliIntraCellHamiltonian (pauliMajorana 0) =
      -(pauliMajorana 1 + pauliMajorana 1) ∧
    commutator pauliIntraCellHamiltonian (pauliMajorana 0) ≠ 0 := by
  exact ⟨interCell_boundary_commutator_zero,
    intraCell_boundary_commutator_exact,
    intraCell_boundary_commutator_ne_zero⟩

/-- Both dimer endpoints conserve the global parity operator even though their
left-boundary commutators differ. -/
theorem dimerization_switch_conserves_global_parity :
    majoranaCommutator pauliFermionParity pauliInterCellHamiltonian = 0 ∧
    majoranaCommutator pauliFermionParity pauliIntraCellHamiltonian = 0 ∧
    majoranaCommutator pauliInterCellHamiltonian (pauliMajorana 0) = 0 ∧
    majoranaCommutator pauliIntraCellHamiltonian (pauliMajorana 0) ≠ 0 := by
  exact ⟨interCell_preserves_fermion_parity,
    intraCell_preserves_fermion_parity,
    interCell_boundary_commutator_zero,
    intraCell_boundary_commutator_ne_zero⟩

/-- Proof-carrying archetype for the finite matrix dimerization switch. -/
def pauliDimerizationSwitchArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.Quantum.KitaevDimerizationSwitch.pauliDimerizationSwitchArchetype
  phase := 63
  claim := fun _ =>
    majoranaCommutator pauliInterCellHamiltonian (pauliMajorana 0) = 0 ∧
    majoranaCommutator pauliIntraCellHamiltonian (pauliMajorana 0) =
      -(pauliMajorana 1 + pauliMajorana 1) ∧
    commutator pauliIntraCellHamiltonian (pauliMajorana 0) ≠ 0
  evidence := fun _ => pauli_dimerization_switch_operator_laws

#register_archetype pauliDimerizationSwitchArchetype
#audit_archetype pauliDimerizationSwitchArchetype

theorem pauli_dimerization_switch_archetype_proved :
    pauliDimerizationSwitchArchetype.claim () :=
  TypedArchetype.discharge pauliDimerizationSwitchArchetype ()

end InfoGeometry.Quantum.KitaevDimerizationSwitch

end
