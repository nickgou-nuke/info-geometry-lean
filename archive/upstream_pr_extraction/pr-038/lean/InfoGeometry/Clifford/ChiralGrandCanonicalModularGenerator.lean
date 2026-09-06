import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

/-!
# The concrete chiral grand-canonical modular generator

This file stays on the repository's native carrier
`InfoGeometry.Clifford.Cl44`.  It does not identify that carrier with the
`AlgebraEnd H` carrier used by the Souriau/Tomita analytic lane.  The bridge
provided here is therefore the exact algebraic part available without adding
an unproved representation or completion map.
-/

namespace InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.ChiralLorentzFockQuadratic
open InfoGeometry.Clifford.Cl44Witt

/-! ### Conservation on the concrete `Cl44` operator carrier -/

theorem grandCanonicalGenerator_commutator_totalNumber_conserved
    (H : Operator) (beta μ μχ : ℝ)
    (hH : algebraCommutator H totalNumber = 0) :
    algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) totalNumber = 0 := by
  unfold grandCanonicalModularGenerator
  have hG : algebraCommutator
      (grandCanonicalGenerator H μ μχ) totalNumber = 0 :=
    totalNumber_commutator_of_grandCanonicalGenerator H μ μχ hH
  unfold algebraCommutator at hG ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, hG, smul_zero]

theorem grandCanonicalModularGenerator_conserves_number_and_chiral_charge
    (H : Operator) (beta μ μχ : ℝ)
    (hNumber : algebraCommutator H totalNumber = 0)
    (hChiral : algebraCommutator H chiralCharge = 0) :
    algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) totalNumber = 0 ∧
      algebraCommutator
        (grandCanonicalModularGenerator H beta μ μχ) chiralCharge = 0 := by
  exact ⟨
    grandCanonicalGenerator_commutator_totalNumber_conserved H beta μ μχ hNumber,
    grandCanonicalModularGenerator_commutator_chiralCharge H beta μ μχ hChiral⟩

/-! ### The two native sheet energies -/

theorem freeGrandCanonicalModularGenerator_commutator_annihilation_plus
    (Eplus Eminus μplus μminus beta : ℝ) :
    algebraCommutator
        (grandCanonicalModularGenerator
          (freeSheetHamiltonian Eplus Eminus) beta
          ((μplus + μminus) / 2) ((μplus - μminus) / 2)) (a 0) =
      -((beta * (Eplus - μplus)) • a 0) := by
  unfold grandCanonicalModularGenerator
  have h := freeGrandCanonicalGenerator_commutator_annihilation_plus
    Eplus Eminus μplus μminus
  unfold freeGrandCanonicalGenerator at h
  unfold algebraCommutator at h ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, h]
  simp [smul_smul]

theorem freeGrandCanonicalModularGenerator_commutator_annihilation_minus
    (Eplus Eminus μplus μminus beta : ℝ) :
    algebraCommutator
        (grandCanonicalModularGenerator
          (freeSheetHamiltonian Eplus Eminus) beta
          ((μplus + μminus) / 2) ((μplus - μminus) / 2)) (a 1) =
      -((beta * (Eminus - μminus)) • a 1) := by
  unfold grandCanonicalModularGenerator
  have h := freeGrandCanonicalGenerator_commutator_annihilation_minus
    Eplus Eminus μplus μminus
  unfold freeGrandCanonicalGenerator at h
  unfold algebraCommutator at h ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, h]
  simp [smul_smul]

theorem freeGrandCanonicalModularGenerator_commutator_creation_plus
    (Eplus Eminus μplus μminus beta : ℝ) :
    algebraCommutator
        (grandCanonicalModularGenerator
          (freeSheetHamiltonian Eplus Eminus) beta
          ((μplus + μminus) / 2) ((μplus - μminus) / 2)) (adag 0) =
      (beta * (Eplus - μplus)) • adag 0 := by
  unfold grandCanonicalModularGenerator
  have h := freeGrandCanonicalGenerator_commutator_creation_plus
    Eplus Eminus μplus μminus
  unfold freeGrandCanonicalGenerator at h
  unfold algebraCommutator at h ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, h]
  simp [smul_smul]

theorem freeGrandCanonicalModularGenerator_commutator_creation_minus
    (Eplus Eminus μplus μminus beta : ℝ) :
    algebraCommutator
        (grandCanonicalModularGenerator
          (freeSheetHamiltonian Eplus Eminus) beta
          ((μplus + μminus) / 2) ((μplus - μminus) / 2)) (adag 1) =
      (beta * (Eminus - μminus)) • adag 1 := by
  unfold grandCanonicalModularGenerator
  have h := freeGrandCanonicalGenerator_commutator_creation_minus
    Eplus Eminus μplus μminus
  unfold freeGrandCanonicalGenerator at h
  unfold algebraCommutator at h ⊢
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [← smul_sub, h]
  simp [smul_smul]

end InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
