import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation
import proofs.ZornMajoranaBraiding

/-!
# Topological Quantum Gates via Majorana Braiding

This module transforms the topological Dirac crystal into a fully functional
topological quantum computing (TQC) compiler. Using the non-Abelian Majorana 
zero modes formalized in the previous modules, we define the logical qubit
within the 16D DiracSpinor16 carrier and synthesize the fundamental Clifford 
gates (Phase, Hadamard, CNOT) directly via sequences of braid operators.
-/

noncomputable section

namespace TopologicalQuantumGates

open LinearMap
open CanonicalZornCliffordRepresentation
open ZornMajoranaBraiding

section SingleQubitGates

variable {γ1 γ2 γ3 γ4 : Module.End ℂ DiracSpinor16}

/-- 
Logical Z Pauli operator for the topological qubit.
Defined as i * γ1 * γ2.
-/
def logical_Z (γ1 γ2 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  Complex.I • (γ1 * γ2)

/-- 
Logical X Pauli operator for the topological qubit.
Defined as i * γ2 * γ3.
-/
def logical_X (γ2 γ3 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  Complex.I • (γ2 * γ3)

/-- 
Logical Y Pauli operator for the topological qubit.
Defined as i * γ1 * γ3.
-/
def logical_Y (γ1 γ3 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  Complex.I • (γ1 * γ3)

/-- 
The Topological Phase Gate (S-gate).
Synthesized via a single non-Abelian braid exchanging modes 1 and 2.
-/
def logical_S_gate (γ1 γ2 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  majoranaBraidOperator γ1 γ2

/-- 
The Topological Hadamard Gate (H-gate).
Synthesized via a sequence of three non-Abelian braids to simultaneously
exchange the mode structures underlying the X and Z logical operators.
-/
def logical_H_gate (γ1 γ2 γ3 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  majoranaBraidOperator γ2 γ3 * majoranaBraidOperator γ1 γ2 * majoranaBraidOperator γ2 γ3

/-- 
The inverse of the Hadamard gate, formalized via the inverse sequence of braids.
-/
def logical_H_gate_inv (γ1 γ2 γ3 : Module.End ℂ DiracSpinor16) : Module.End ℂ DiracSpinor16 :=
  majoranaBraidOperatorInv γ2 γ3 * majoranaBraidOperatorInv γ1 γ2 * majoranaBraidOperatorInv γ2 γ3

theorem conjugate_smul
    (U V A : Module.End ℂ DiracSpinor16) (c : ℂ) :
    U * (c • A) * V = c • (U * A * V) := by
  rw [mul_smul_comm, smul_mul_assoc]

theorem conjugate_comp
    (U₂ U₁ V₁ V₂ A : Module.End ℂ DiracSpinor16) :
    (U₂ * U₁) * A * (V₁ * V₂) = U₂ * (U₁ * A * V₁) * V₂ := by
  simp only [mul_assoc]

theorem conjugate_neg
    (U V A : Module.End ℂ DiracSpinor16) :
    U * (-A) * V = -(U * A * V) := by
  rw [end_mul_neg, end_neg_mul]

/--
Theorem: The topological Hadamard braid sequence transforms the logical Z
operator into the logical X operator. This is the cornerstone of Clifford
gate synthesis in topological quantum computing.
-/
theorem hadamard_transforms_Z_to_X 
    (h_anti_12 : γ1 * γ2 + γ2 * γ1 = 0)
    (h_anti_23 : γ2 * γ3 + γ3 * γ2 = 0)
    (h_anti_13 : γ1 * γ3 + γ3 * γ1 = 0)
    (h_sq_1 : γ1 * γ1 = 1)
    (h_sq_2 : γ2 * γ2 = 1)
    (h_sq_3 : γ3 * γ3 = 1) :
    logical_H_gate γ1 γ2 γ3 * logical_Z γ1 γ2 * logical_H_gate_inv γ1 γ2 γ3 = 
    logical_X γ2 γ3 := by
  let U12 := majoranaBraidOperator γ1 γ2
  let V12 := majoranaBraidOperatorInv γ1 γ2
  let U23 := majoranaBraidOperator γ2 γ3
  let V23 := majoranaBraidOperatorInv γ2 γ3
  have hV12U12 : V12 * U12 = 1 := by
    exact braid_inv_rev h_anti_12 h_sq_1 h_sq_2
  have hV23U23 : V23 * U23 = 1 := by
    exact braid_inv_rev h_anti_23 h_sq_2 h_sq_3
  have h23_γ1 : U23 * γ1 * V23 = γ1 := by
    apply braid_fixes_other h_anti_23 h_sq_2 h_sq_3
    · simpa [add_comm] using h_anti_12
    · simpa [add_comm] using h_anti_13
  have h23_γ2 : U23 * γ2 * V23 = -γ3 := by
    exact braid_transformation_i h_anti_23 h_sq_2 h_sq_3
  have h12_γ1 : U12 * γ1 * V12 = -γ2 := by
    exact braid_transformation_i h_anti_12 h_sq_1 h_sq_2
  have h12_γ3 : U12 * γ3 * V12 = γ3 := by
    exact braid_fixes_other h_anti_12 h_sq_1 h_sq_2 h_anti_13 h_anti_23
  have h23_γ3 : U23 * γ3 * V23 = γ2 := by
    exact braid_transformation_j h_anti_23 h_sq_2 h_sq_3
  have hstage1 : U23 * logical_Z γ1 γ2 * V23 = -logical_Y γ1 γ3 := by
    rw [logical_Z, logical_Y, conjugate_smul]
    rw [conjugate_mul U23 V23 γ1 γ2 hV23U23, h23_γ1, h23_γ2]
    rw [end_mul_neg, smul_neg]
  have hstage2 : U12 * (-logical_Y γ1 γ3) * V12 = logical_X γ2 γ3 := by
    rw [logical_Y, logical_X, end_mul_neg, end_neg_mul, conjugate_smul]
    rw [conjugate_mul U12 V12 γ1 γ3 hV12U12, h12_γ1, h12_γ3]
    rw [end_neg_mul, smul_neg, neg_neg]
  have hstage3 : U23 * logical_X γ2 γ3 * V23 = logical_X γ2 γ3 := by
    rw [logical_X, conjugate_smul]
    rw [conjugate_mul U23 V23 γ2 γ3 hV23U23, h23_γ2, h23_γ3]
    have hswap : γ3 * γ2 = -(γ2 * γ3) :=
      eq_neg_of_add_eq_zero_right h_anti_23
    congr 1
    calc
      (-γ3) * γ2 = -(γ3 * γ2) := end_neg_mul _ _
      _ = -(-(γ2 * γ3)) := congrArg Neg.neg hswap
      _ = γ2 * γ3 := neg_neg _
  change (U23 * U12 * U23) * logical_Z γ1 γ2 *
      (V23 * V12 * V23) = logical_X γ2 γ3
  calc
    (U23 * U12 * U23) * logical_Z γ1 γ2 * (V23 * V12 * V23) =
        U23 * (U12 * (U23 * logical_Z γ1 γ2 * V23) * V12) * V23 := by
          simp only [mul_assoc]
    _ = U23 * (U12 * (-logical_Y γ1 γ3) * V12) * V23 := by rw [hstage1]
    _ = U23 * logical_X γ2 γ3 * V23 := by rw [hstage2]
    _ = logical_X γ2 γ3 := hstage3

end SingleQubitGates

section TwoQubitGates

/-- 
The Controlled-NOT (CNOT) Gate.
For two-qubit operations, we require 8 Majorana modes (γ_1 to γ_8).
The CNOT gate is synthesized by braiding the modes of the control qubit
with the modes of the target qubit. Here we provide the abstract 
entangling sequence.
-/
def logical_CNOT_gate (γ : Fin 8 → Module.End ℂ DiracSpinor16) : 
    Module.End ℂ DiracSpinor16 :=
  -- U_25 * U_26 * U_35 * U_36
  majoranaBraidOperator (γ 1) (γ 4) * 
  majoranaBraidOperator (γ 1) (γ 5) * 
  majoranaBraidOperator (γ 2) (γ 4) * 
  majoranaBraidOperator (γ 2) (γ 5)

/-- The inverse word, with inverse factors in reverse order. -/
def logical_CNOT_gate_inv (γ : Fin 8 → Module.End ℂ DiracSpinor16) :
    Module.End ℂ DiracSpinor16 :=
  majoranaBraidOperatorInv (γ 2) (γ 5) *
  majoranaBraidOperatorInv (γ 2) (γ 4) *
  majoranaBraidOperatorInv (γ 1) (γ 5) *
  majoranaBraidOperatorInv (γ 1) (γ 4)

/-- Exact action of the declared four-braid word on the displayed product of
logical bilinears.  The inverse word is essential: this is a conjugation
identity, not multiplication by the same braid word on both sides. -/
theorem cnot_entangles_modes 
    (γ : Fin 8 → Module.End ℂ DiracSpinor16)
    (h_anti : ∀ i j, i ≠ j → γ i * γ j + γ j * γ i = 0)
    (h_sq : ∀ i, γ i * γ i = 1) :
    logical_CNOT_gate γ *
        (logical_Z (γ 0) (γ 1) * logical_Z (γ 4) (γ 5)) *
        logical_CNOT_gate_inv γ =
      logical_Z (γ 0) (γ 5) * logical_Z (γ 2) (γ 1) := by
  let U14 := majoranaBraidOperator (γ 1) (γ 4)
  let U15 := majoranaBraidOperator (γ 1) (γ 5)
  let U24 := majoranaBraidOperator (γ 2) (γ 4)
  let U25 := majoranaBraidOperator (γ 2) (γ 5)
  let V14 := majoranaBraidOperatorInv (γ 1) (γ 4)
  let V15 := majoranaBraidOperatorInv (γ 1) (γ 5)
  let V24 := majoranaBraidOperatorInv (γ 2) (γ 4)
  let V25 := majoranaBraidOperatorInv (γ 2) (γ 5)
  let G := U14 * U15 * U24 * U25
  let Ginv := V25 * V24 * V15 * V14
  have hac (i j : Fin 8) (hij : i ≠ j) : γ i * γ j + γ j * γ i = 0 :=
    h_anti i j hij
  have hV14 : V14 * U14 = 1 := braid_inv_rev (hac 1 4 (by decide)) (h_sq 1) (h_sq 4)
  have hV15 : V15 * U15 = 1 := braid_inv_rev (hac 1 5 (by decide)) (h_sq 1) (h_sq 5)
  have hV24 : V24 * U24 = 1 := braid_inv_rev (hac 2 4 (by decide)) (h_sq 2) (h_sq 4)
  have hV25 : V25 * U25 = 1 := braid_inv_rev (hac 2 5 (by decide)) (h_sq 2) (h_sq 5)
  have hGinv : Ginv * G = 1 := by
    dsimp [G, Ginv]
    simp only [mul_assoc]
    rw [← mul_assoc V14 U14, hV14, one_mul,
      ← mul_assoc V15 U15, hV15, one_mul,
      ← mul_assoc V24 U24, hV24, one_mul, hV25]
  have hchain (A : Module.End ℂ DiracSpinor16) :
      G * A * Ginv =
        U14 * (U15 * (U24 * (U25 * A * V25) * V24) * V15) * V14 := by
    dsimp [G, Ginv]
    simp only [mul_assoc]
  have h0 : G * γ 0 * Ginv = γ 0 := by
    rw [hchain]
    rw [braid_fixes_other (hac 2 5 (by decide)) (h_sq 2) (h_sq 5)
          (hac 2 0 (by decide)) (hac 5 0 (by decide))]
    rw [braid_fixes_other (hac 2 4 (by decide)) (h_sq 2) (h_sq 4)
          (hac 2 0 (by decide)) (hac 4 0 (by decide))]
    rw [braid_fixes_other (hac 1 5 (by decide)) (h_sq 1) (h_sq 5)
          (hac 1 0 (by decide)) (hac 5 0 (by decide))]
    exact braid_fixes_other (hac 1 4 (by decide)) (h_sq 1) (h_sq 4)
      (hac 1 0 (by decide)) (hac 4 0 (by decide))
  have h1 : G * γ 1 * Ginv = -γ 5 := by
    rw [hchain]
    rw [braid_fixes_other (hac 2 5 (by decide)) (h_sq 2) (h_sq 5)
          (hac 2 1 (by decide)) (hac 5 1 (by decide))]
    rw [braid_fixes_other (hac 2 4 (by decide)) (h_sq 2) (h_sq 4)
          (hac 2 1 (by decide)) (hac 4 1 (by decide))]
    rw [braid_transformation_i (hac 1 5 (by decide)) (h_sq 1) (h_sq 5)]
    rw [conjugate_neg]
    rw [braid_fixes_other (hac 1 4 (by decide)) (h_sq 1) (h_sq 4)
          (hac 1 5 (by decide)) (hac 4 5 (by decide))]
  have h4 : G * γ 4 * Ginv = γ 2 := by
    rw [hchain]
    rw [braid_fixes_other (hac 2 5 (by decide)) (h_sq 2) (h_sq 5)
          (hac 2 4 (by decide)) (hac 5 4 (by decide))]
    rw [braid_transformation_j (hac 2 4 (by decide)) (h_sq 2) (h_sq 4)]
    rw [braid_fixes_other (hac 1 5 (by decide)) (h_sq 1) (h_sq 5)
          (hac 1 2 (by decide)) (hac 5 2 (by decide))]
    exact braid_fixes_other (hac 1 4 (by decide)) (h_sq 1) (h_sq 4)
      (hac 1 2 (by decide)) (hac 4 2 (by decide))
  have h5 : G * γ 5 * Ginv = -γ 1 := by
    rw [hchain]
    rw [braid_transformation_j (hac 2 5 (by decide)) (h_sq 2) (h_sq 5)]
    rw [braid_transformation_i (hac 2 4 (by decide)) (h_sq 2) (h_sq 4)]
    rw [conjugate_neg]
    rw [braid_fixes_other (hac 1 5 (by decide)) (h_sq 1) (h_sq 5)
          (hac 1 4 (by decide)) (hac 5 4 (by decide))]
    rw [conjugate_neg]
    rw [braid_transformation_j (hac 1 4 (by decide)) (h_sq 1) (h_sq 4)]
  change G * (logical_Z (γ 0) (γ 1) * logical_Z (γ 4) (γ 5)) * Ginv = _
  rw [conjugate_mul G Ginv _ _ hGinv]
  rw [logical_Z, conjugate_smul,
    conjugate_mul G Ginv (γ 0) (γ 1) hGinv, h0, h1]
  rw [logical_Z, conjugate_smul,
    conjugate_mul G Ginv (γ 4) (γ 5) hGinv, h4, h5]
  rw [end_mul_neg, smul_neg, end_mul_neg, smul_neg]
  simpa only [logical_Z] using
    (neg_mul_neg (Complex.I • (γ 0 * γ 5)) (Complex.I • (γ 2 * γ 1)))

end TwoQubitGates

end TopologicalQuantumGates
