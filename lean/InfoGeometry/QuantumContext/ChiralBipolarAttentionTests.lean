import InfoGeometry.QuantumContext.ChiralBipolarAttention
import InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-!
# Regression Tests and Axiom Audits for Chiral Bipolar Attention & Causal Poset

This module exercises the concrete evaluations and prints the transitive axiom dependencies
of the newly synthesized canonical modules:
1. `ChiralBipolarAttention.lean`
2. `CanonicalArchetypeCausalPoset.lean`

All tests are kernel-checked with 0 sorry and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.ChiralBipolarAttentionTests

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling
open InfoGeometry.QuantumContext.TransformerLatentSpace
open InfoGeometry.QuantumContext.ChiralBipolarAttention
open InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-- Concrete test matrix with non-zero diagonal entries (simulating softmax attention). -/
def testAttentionMatrix : Mat2 := !![1, 2; 3, 4]

/-- Test that chiralBipolar eliminates the diagonal entries exactly. -/
example : chiralBipolar testAttentionMatrix = !![0, 2; 3, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

/-- Test that chiralBipolar satisfies the Peirce sector swap on testAttentionMatrix. -/
example : leftProjection * chiralBipolar testAttentionMatrix =
    chiralBipolar testAttentionMatrix * complementIdempotent leftProjection :=
  chiralBipolar_swaps testAttentionMatrix

/-- Test that chiralBipolar strictly anticommutes with the chiral grading. -/
example : grading leftProjection * chiralBipolar testAttentionMatrix +
    chiralBipolar testAttentionMatrix * grading leftProjection = 0 :=
  chiralBipolar_anticommutes testAttentionMatrix

/-- Symmetric balanced test coupling with mass m = 2. -/
def balancedTestMatrix : Mat2 := !![5, 2; 2, 5]

theorem balancedTestMatrix_is_balanced : IsBalancedCoupling balancedTestMatrix 2 := by
  dsimp [IsBalancedCoupling, balancedTestMatrix]
  norm_num

/-- Test that the balanced chiral bipolar operator squares to 2^2 = 4. -/
example : chiralBipolar balancedTestMatrix * chiralBipolar balancedTestMatrix =
    algebraMap ℝ Mat2 (2 ^ 2) :=
  chiralBipolar_square_of_balanced balancedTestMatrix 2 balancedTestMatrix_is_balanced

/-- Test that for momentum p = 3 and mass m = 2, the Hamiltonian squares to 3^2 + 2^2 = 13. -/
example : (3 • grading leftProjection + chiralBipolar balancedTestMatrix) *
    (3 • grading leftProjection + chiralBipolar balancedTestMatrix) =
    algebraMap ℝ Mat2 (3 ^ 2 + 2 ^ 2) :=
  chiralBipolar_hamiltonian_square balancedTestMatrix 3 2 balancedTestMatrix_is_balanced

/-- Concrete 4-vector potential test: A = (5, 1, 2, 4). -/
def testFourVector : Fin 4 → ℝ := ![5, 1, 2, 4]

/-- Test that the determinant of the 4-vector matrix matches Minkowski norm:
    5^2 - 1^2 + 2^2 - 4^2 = 25 - 1 + 4 - 16 = 12. -/
example : (fourVectorPotentialMatrix testFourVector).det = 12 := by
  rw [fourVector_det_minkowski]
  norm_num [testFourVector]

/-! ### Axiom Inspections: Ensuring 100% Kernel Truth -/

#print axioms chiralBipolar_swaps
#print axioms chiralBipolar_anticommutes
#print axioms chiralBipolar_square
#print axioms chiralBipolar_hamiltonian_square
#print axioms fourVector_det_minkowski
#print axioms colimit_precedes_all
#print axioms obstruction_precedes_chiral_repair
#print axioms causal_poset_acyclic

end InfoGeometry.QuantumContext.ChiralBipolarAttentionTests
