/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.FiniteWeightedSplitKreinAdjoint
import InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit
import InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
import Mathlib.Tactic

/-!
# Finite weighted split operators in a matrix stage

The finite weighted doubled operator is represented by the block matrix
`diag(P, weightedAdjoint π P)`. An explicit equivalence places this real
matrix in one of the repository's finite complex matrix stages, whose
canonical inclusion then gives a colimit algebra element.

This is a representation of one finite doubled operator. It is not the tower
bonding map `A ↦ A ⊗ I₂`, which gives `diag(A,A)`, and this file does not
define an operator action or weighted pairing on the colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Probability.FiniteWeightedSplitKreinMatrixStage

open InfoGeometry.Probability
open InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

/-- The block matrix encoding the finite split weighted operator. -/
def splitWeightedBlock (π : ι → ℝ) (P : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks P 0 0 (weightedAdjoint π P)

/-- Encode the two real coordinate sheets as one function on the disjoint sum. -/
def splitCarrierVector (x : (ι → ℝ) × (ι → ℝ)) : ι ⊕ ι → ℝ :=
  Sum.elim x.1 x.2

/-- Complexify and reindex a vector on the doubled finite carrier. -/
def splitCarrierVectorStage (e : ι ⊕ ι ≃ BitWord n)
    (x : (ι → ℝ) × (ι → ℝ)) : BitWord n → ℂ :=
  fun b => (algebraMap ℝ ℂ) (splitCarrierVector x (e.symm b))

/-- Reindex and complexify the finite block representation into an explicitly
chosen repository matrix stage. The equivalence records the finite dimension
identification in the theorem data. -/
def splitWeightedBlockStage (n : ℕ) (e : ι ⊕ ι ≃ BitWord n)
    (π : ι → ℝ) (P : Matrix ι ι ℝ) : Stage n :=
  realMatrixToComplexStage n e (splitWeightedBlock π P)

omit [DecidableEq ι] in
/-- The block matrix acts on the concatenated vector by the existing split
weighted operator, with its original matrix on the first sheet and weighted
adjoint on the second. -/
theorem splitWeightedBlock_mulVec (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (x : (ι → ℝ) × (ι → ℝ)) :
    splitWeightedBlock π P *ᵥ splitCarrierVector x =
      splitCarrierVector (splitWeightedOperator π P x) := by
  ext s
  cases s <;>
    simp [splitWeightedBlock, splitCarrierVector, splitWeightedOperator,
      Matrix.fromBlocks_mulVec]

/-- The complexified finite-stage matrix acts on the reindexed complexified
vector exactly as the original doubled operator acts before complexification.
This is the action-level compatibility between the two finite carriers. -/
theorem splitWeightedBlockStage_mulVec (n : ℕ)
    (e : ι ⊕ ι ≃ BitWord n) (π : ι → ℝ) (P : Matrix ι ι ℝ)
    (x : (ι → ℝ) × (ι → ℝ)) :
    splitWeightedBlockStage n e π P *ᵥ splitCarrierVectorStage e x =
      splitCarrierVectorStage e (splitWeightedOperator π P x) := by
  ext b
  rw [Matrix.mulVec_apply_eq_sum]
  calc
    (∑ c : BitWord n,
        splitWeightedBlockStage n e π P b c * splitCarrierVectorStage e x c) =
        ∑ s : ι ⊕ ι,
          splitWeightedBlockStage n e π P b (e s) *
            splitCarrierVectorStage e x (e s) := by
              exact (Equiv.sum_comp e (fun c : BitWord n =>
                splitWeightedBlockStage n e π P b c *
                  splitCarrierVectorStage e x c)).symm
    _ = ∑ s : ι ⊕ ι,
          (algebraMap ℝ ℂ) (splitWeightedBlock π P (e.symm b) s) *
            (algebraMap ℝ ℂ) (splitCarrierVector x s) := by
              apply Finset.sum_congr rfl
              intro s hs
              have hmatrix : splitWeightedBlockStage n e π P b (e s) =
                  (algebraMap ℝ ℂ) (splitWeightedBlock π P (e.symm b) s) := by
                simp [splitWeightedBlockStage, realMatrixToComplexStage,
                  realMatrixComplexifyAlgHom, RingHom.mapMatrix_apply]
              have hvector : splitCarrierVectorStage e x (e s) =
                  (algebraMap ℝ ℂ) (splitCarrierVector x s) := by
                simp [splitCarrierVectorStage]
              rw [hmatrix, hvector]
    _ = (algebraMap ℝ ℂ)
          ((splitWeightedBlock π P *ᵥ splitCarrierVector x) (e.symm b)) := by
          calc
            _ = ∑ s : ι ⊕ ι,
                (algebraMap ℝ ℂ)
                    (splitWeightedBlock π P (e.symm b) s * splitCarrierVector x s) := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [map_mul]
            _ = (algebraMap ℝ ℂ)
                  (∑ s : ι ⊕ ι,
                    splitWeightedBlock π P (e.symm b) s * splitCarrierVector x s) := by
                  rw [map_sum]
            _ = (algebraMap ℝ ℂ)
                  ((splitWeightedBlock π P *ᵥ splitCarrierVector x) (e.symm b)) := by
                  rw [Matrix.mulVec_apply_eq_sum]
    _ = (algebraMap ℝ ℂ)
          (splitCarrierVector (splitWeightedOperator π P x) (e.symm b)) := by
          rw [congrFun (splitWeightedBlock_mulVec π P x) (e.symm b)]
    _ = splitCarrierVectorStage e (splitWeightedOperator π P x) b := rfl

/-- The represented finite-stage matrix in the existing algebraic Cuntz matrix
colimit. The stage equivalence and canonical stage injection are explicit; this
does not assert a vector action or a descended Krein pairing on the colimit. -/
def splitWeightedBlockCuntzColimit (n : ℕ) (e : ι ⊕ ι ≃ BitWord n)
    (π : ι → ℝ) (P : Matrix ι ι ℝ) : Carrier :=
  stageInjection n (stageStarAlgEquiv n (splitWeightedBlockStage n e π P))

end InfoGeometry.Probability.FiniteWeightedSplitKreinMatrixStage

end
