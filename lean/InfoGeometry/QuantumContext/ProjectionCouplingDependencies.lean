/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.QuantumContext.ProjectionCouplingDependencies

inductive Archetype
  | idempotent
  | fixedRange
  | hiddenKernel
  | uniqueDecomposition
  | symmetricInnerProduct
  | orthogonalDecomposition
  | sectorSwap
  | signedMomentum
  | anticommutation
  | scalarCouplingSquare
  | hamiltonianSquare
  | positiveSoftmax
  | softmaxObstruction
  deriving DecidableEq

instance : Fintype Archetype :=
  Fintype.ofList
    [.idempotent, .fixedRange, .hiddenKernel, .uniqueDecomposition,
      .symmetricInnerProduct, .orthogonalDecomposition, .sectorSwap,
      .signedMomentum, .anticommutation, .scalarCouplingSquare,
      .hamiltonianSquare, .positiveSoftmax, .softmaxObstruction]
    (by intro x; cases x <;> simp)

def prerequisites : Archetype → Finset ℕ
  | .idempotent => {0}
  | .fixedRange => {0, 1}
  | .hiddenKernel => {0, 2}
  | .uniqueDecomposition => {0, 1, 2, 3}
  | .symmetricInnerProduct => {4}
  | .orthogonalDecomposition => {0, 1, 2, 3, 4, 5}
  | .sectorSwap => {6}
  | .signedMomentum => {7}
  | .anticommutation => {6, 7, 8}
  | .scalarCouplingSquare => {9}
  | .hamiltonianSquare => {0, 6, 7, 8, 9, 10}
  | .positiveSoftmax => {11}
  | .softmaxObstruction => {0, 6, 11, 12}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem projection_dependencies :
    Archetype.fixedRange ≤ Archetype.uniqueDecomposition ∧
      Archetype.hiddenKernel ≤ Archetype.uniqueDecomposition ∧
      Archetype.symmetricInnerProduct ≤ Archetype.orthogonalDecomposition := by decide

theorem coupling_dependencies :
    Archetype.sectorSwap ≤ Archetype.anticommutation ∧
      Archetype.signedMomentum ≤ Archetype.anticommutation ∧
      Archetype.anticommutation ≤ Archetype.hamiltonianSquare ∧
      Archetype.scalarCouplingSquare ≤ Archetype.hamiltonianSquare := by decide

theorem range_and_kernel_incomparable :
    ¬ Archetype.fixedRange ≤ Archetype.hiddenKernel ∧
      ¬ Archetype.hiddenKernel ≤ Archetype.fixedRange := by decide

theorem softmax_does_not_supply_swap :
    ¬ Archetype.sectorSwap ≤ Archetype.positiveSoftmax := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right := le_antisymm forward backward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–4 (`idempotent`, `fixedRange`, `hiddenKernel`, `uniqueDecomposition`):**
Idempotent projector `P * P = P` fixes the `P`-range (`P * (P * X) = P * X`), annihilates the
`(1 - P)`-kernel (`P * ((1 - P) * X) = 0`), and decomposes any operator `X` into its
four Peirce blocks `evenGrade P X + oddGrade P X = X`. -/
theorem archetype_projection_range_kernel_and_decomposition
    {P : B} (hP : P * P = P) (X : B) :
    P * (P * X) = P * X ∧
    P * ((1 - P) * X) = 0 ∧
    (1 - P) * (P * X) = 0 ∧
    evenGrade P X + oddGrade P X = X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · simp only [evenGrade, oddGrade]; peirce_nf hP

/-- **Archetypes 5–6 (`symmetricInnerProduct`, `orthogonalDecomposition`):**
Under the symmetric Jordan anticommutator `anticomm`, the complementary projectors `P` and `1 - P`
are orthogonal (`anticomm P (1 - P) = 0`), while the grading involution `S_P = P - (1 - P)`
satisfies `S_P² = 1` and `X + S_P * X * S_P = 2 • evenGrade P X`. -/
theorem archetype_symmetric_jordan_orthogonality_and_grading
    {P : B} (hP : P * P = P) (X : B) :
    anticomm P (1 - P) = 0 ∧
    invS P * invS P = 1 ∧
    X + invS P * X * invS P = (2 : ℤ) • evenGrade P X ∧
    X - invS P * X * invS P = (2 : ℤ) • oddGrade P X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetypes 7–9 (`sectorSwap`, `signedMomentum`, `anticommutation`):**
Off-diagonal sector swap `Φ = N_+ + N_-` and signed dipole `J = N_+ - N_-` anticommute with
the grading involution `S_P` (`{S_P, Φ} = 0`, `{S_P, J} = 0`) and mutually anticommute
(`{Φ, J} = 0`). -/
theorem archetype_sector_swap_and_signed_momentum_anticommutation
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    invS P * genPhi P A C = genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetypes 10–11 (`scalarCouplingSquare`, `hamiltonianSquare`):**
Quadratic coupling squares of the off-diagonal swap `Φ`, signed dipole `J`, and composite
Dirac/BdG operator `Φ + J`:
`Φ² = V`, `J² = -V`, `(Φ + J)² = 0`, and `(Φ - J)² = 0`. -/
theorem archetype_coupling_and_hamiltonian_squares
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    (genPhi P A C + genJ P A C) * (genPhi P A C + genJ P A C) = 0 ∧
    (genPhi P A C - genJ P A C) * (genPhi P A C - genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetypes 12–13 (`positiveSoftmax`, `softmaxObstruction`):**
Any even-grade diagonal operator `evenGrade P D` commutes with `P` and `S_P`
(`comm P (evenGrade P D) = 0`, `comm (invS P) (evenGrade P D) = 0`) and therefore cannot
generate off-diagonal sector swap (`oddGrade P (evenGrade P D) = 0`), whereas `Φ` has
non-vanishing commutator `comm P Φ = J`. -/
theorem archetype_diagonal_softmax_obstruction_vs_sector_swap
    {P : B} (hP : P * P = P) (A C D : B) :
    comm P (evenGrade P D) = 0 ∧
    comm (invS P) (evenGrade P D) = 0 ∧
    oddGrade P (evenGrade P D) = 0 ∧
    comm P (genPhi P A C) = genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evenGrade]; peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · simp only [evenGrade, oddGrade]; peirce_nf hP
  · peirce_nf hP

/-- **Master Synthesis (`projection_coupling_dependencies_master_synthesis`):**
Unites the partial-order dependency theorems with all 13 non-commutative `[Ring B]`
projection and coupling operator identities. -/
theorem projection_coupling_dependencies_master_synthesis
    {P : B} (hP : P * P = P) (A C D X : B) :
    (Archetype.fixedRange ≤ Archetype.uniqueDecomposition ∧
      Archetype.sectorSwap ≤ Archetype.anticommutation ∧
      Archetype.anticommutation ≤ Archetype.hamiltonianSquare ∧
      ¬ Archetype.sectorSwap ≤ Archetype.positiveSoftmax) ∧
    (evenGrade P X + oddGrade P X = X) ∧
    (anticomm P (1 - P) = 0 ∧ invS P * invS P = 1) ∧
    (anticomm (invS P) (genPhi P A C) = 0 ∧ anticomm (genPhi P A C) (genJ P A C) = 0) ∧
    (genPhi P A C * genPhi P A C = genV P A C ∧ genJ P A C * genJ P A C = -genV P A C) ∧
    (comm P (evenGrade P D) = 0 ∧ comm P (genPhi P A C) = genJ P A C) := by
  have h1 := archetype_projection_range_kernel_and_decomposition hP X
  have h2 := archetype_symmetric_jordan_orthogonality_and_grading hP X
  have h3 := archetype_sector_swap_and_signed_momentum_anticommutation hP A C
  have h4 := archetype_coupling_and_hamiltonian_squares hP A C
  have h5 := archetype_diagonal_softmax_obstruction_vs_sector_swap hP A C D
  exact ⟨⟨projection_dependencies.1, coupling_dependencies.1,
      coupling_dependencies.2.2.1, softmax_does_not_supply_swap⟩,
    h1.2.2.2, ⟨h2.1, h2.2.1⟩, ⟨h3.1, h3.2.2.1⟩, ⟨h4.1, h4.2.1⟩, ⟨h5.1, h5.2.2.2⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.QuantumContext.ProjectionCouplingDependencies
