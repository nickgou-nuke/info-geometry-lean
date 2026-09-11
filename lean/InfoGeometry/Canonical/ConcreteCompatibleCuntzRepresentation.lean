import InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization

/-!
# Concrete compatible Cuntz readout

This is the composition owner: the coherent real Clifford/BitWord matrix
identification is complexified entrywise and then evaluated by the already
proved boundary Cuntz matrix representation.  Thus the infinite map is a
genuine compatible cone, not an axiomatically supplied stage family.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteCompatibleCuntzRepresentation

open InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationRefinementBridge
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism

abbrev Op := BoundedL2Operator

def complexify (n : ℕ) (A : InfoGeometry.Algebra.CliffordBitWordEquivalence.UHFStage n) :
    InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.Stage n :=
  fun i j => algebraMap ℝ ℂ (A i j)

theorem complexify_add (n : ℕ) (A B : UHFStage n) :
    complexify n (A + B) = complexify n A + complexify n B := by
  ext i j
  simp [complexify]

theorem complexify_mul (n : ℕ) (A B : UHFStage n) :
    complexify n (A * B) = complexify n A * complexify n B := by
  ext i j
  simp [complexify, Matrix.mul_apply, map_sum, mul_comm]

theorem complexify_one (n : ℕ) :
    complexify n (1 : UHFStage n) =
      (1 : InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.Stage n) := by
  ext i j
  simp [complexify, Matrix.one_apply]

theorem complexify_zero (n : ℕ) :
    complexify n (0 : UHFStage n) =
      (0 : InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge.Stage n) := by
  ext i j
  simp [complexify]

def stageMap (n : ℕ) :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n →+* Op where
  toFun := fun A => boundaryRep n (complexify n (clStageEquiv n A))
  map_one' := by
    have h : clStageEquiv n (1 : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) = 1 :=
      (clStageEquiv n).map_one
    rw [h, complexify_one, map_one]
  map_mul' A B := by
    have h : clStageEquiv n (A * B) = clStageEquiv n A * clStageEquiv n B :=
      (clStageEquiv n).map_mul A B
    rw [h, complexify_mul]
    exact (boundaryRep n).map_mul _ _
  map_zero' := by
    have h : clStageEquiv n (0 : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) = 0 :=
      (clStageEquiv n).map_zero
    rw [h, complexify_zero, map_zero]
  map_add' A B := by
    have h : clStageEquiv n (A + B) = clStageEquiv n A + clStageEquiv n B :=
      (clStageEquiv n).map_add A B
    rw [h, complexify_add]
    exact (boundaryRep n).map_add _ _

theorem stageMap_matrixUnit (n : ℕ) (i j : BitWord n) :
    stageMap n ((clStageEquiv n).symm (cuntzCoreUnit n i j)) =
      correspondingCuntzWord n i j := by
  change boundaryRep n
      (complexify n (clStageEquiv n ((clStageEquiv n).symm
        (cuntzCoreUnit n i j)))) = _
  rw [AlgEquiv.apply_symm_apply]
  have hunit : complexify n (cuntzCoreUnit n i j) = Matrix.single i j 1 := by
    ext u v
    by_cases hui : i = u <;> by_cases hvj : j = v <;>
      simp [complexify, cuntzCoreUnit, Matrix.single_apply, hui, hvj]
  rw [hunit]
  exact matrixUnit_generator_transport n i j

theorem stageMap_compat (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) :
    stageMap (n + 1) (stageBond n A) = stageMap n A := by
  change boundaryRep (n + 1)
      (complexify (n + 1) (clStageEquiv (n + 1) (stageBond n A))) =
    boundaryRep n (complexify n (clStageEquiv n A))
  rw [clStageEquiv_bond]
  have htransport :
      complexify (n + 1) (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n
        (clStageEquiv n A)) =
        dyadicMatrixEmbedding n (complexify n (clStageEquiv n A)) := by
    have hleft :
        complexify (n + 1) (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n
          (clStageEquiv n A)) =
          ComplexMatrixStage.bondFun n
            (complexify n (clStageEquiv n A)) := by
      ext u v
      by_cases h : u ⟨n, Nat.lt_succ_self n⟩ = v ⟨n, Nat.lt_succ_self n⟩
      · simp [complexify, InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond,
          InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBondFun,
          ComplexMatrixStage.bondFun, h]
      · simp [complexify, InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond,
          InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBondFun,
          ComplexMatrixStage.bondFun, h]
    rw [hleft,
      GenuineMatrixStageMorphism.bondFun_eq_dyadicMatrixEmbedding]
  rw [htransport]
  exact Eq.symm (boundaryRep_bond_compatible n _)

def representation :
    InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework.CompatibleCuntzRepresentation
      (Op := Op) where
  cuntz := {
    S := fun i => match i with
      | ⟨0, _⟩ => vLeft
      | ⟨1, _⟩ => vRight
    isometry := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact vLeft_adjoint_comp_vLeft
      · exact vLeft_adjoint_comp_vRight
      · exact vRight_adjoint_comp_vLeft
      · exact vRight_adjoint_comp_vRight
    range_sum := by
      rw [Fin.sum_univ_two]
      change vLeft.comp (normalizedPrependBitLpAdjoint false) +
          vRight.comp (normalizedPrependBitLpAdjoint true) = _
      rw [add_comm]
      simpa [vLeft, vRight, add_comm] using normalizedPrependBitLp_partition }
  stageMap := stageMap
  stage_compat := stageMap_compat
  seed := 1

def colimitRepresentation :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →+* Op :=
  InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework.CompatibleCuntzRepresentation.representation
    representation

@[simp] theorem colimitRepresentation_stage (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) :
    colimitRepresentation (ofStage n A) = stageMap n A := by
  exact InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework.CompatibleCuntzRepresentation.representation_stage
    representation n A

end InfoGeometry.Canonical.ConcreteCompatibleCuntzRepresentation

end noncomputable section
