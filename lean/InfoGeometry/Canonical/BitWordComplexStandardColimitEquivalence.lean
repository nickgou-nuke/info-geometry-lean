import Mathlib.Tactic
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
import InfoGeometry.Canonical.CuntzMatrixTraceTower

noncomputable section

namespace InfoGeometry.Canonical.BitWordComplexStandardColimitEquivalence

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge

/-- The standard complex matrix tower, viewed as a one-step ring system. -/
abbrev StandardStage (n : Nat) := MatrixStage n

/-- Ring-hom bonding maps induced by the native star-algebra embeddings. -/
abbrev standardBond (n : Nat) : StandardStage n →+* StandardStage (n + 1) :=
  (concreteStep n).toRingHom

/-- Algebraic direct limit of the standard `Fin (2^n)` complex matrix tower. -/
abbrev StandardColimit := DirectLimitSuperClosure standardBond

/-- Canonical map from a standard finite stage into its algebraic direct limit. -/
def standardToColimit (n : Nat) : StandardStage n →+* StandardColimit :=
  directLimitOf standardBond n

/-- Stagewise forward map into the standard algebraic direct limit. -/
def forwardCone (n : Nat) : ComplexMatrixStage.Stage n →+* StandardColimit :=
  (standardToColimit n).comp (stageStarAlgEquiv n).toRingEquiv.toRingHom

/-- The forward stage maps form a compatible cone. -/
theorem forwardCone_compatible :
    CompatibleCone ComplexMatrixStage.bond forwardCone := by
  intro n A
  change standardToColimit (n + 1)
      (stageStarAlgEquiv (n + 1) (ComplexMatrixStage.bond n A)) =
    standardToColimit n (stageStarAlgEquiv n A)
  rw [stageStarAlgEquiv_bond_hom]
  exact directLimitOf_bond standardBond n (stageStarAlgEquiv n A)

/-- Global homomorphism induced by the stagewise natural equivalence. -/
noncomputable def toStandardColimit :
    ComplexMatrixStage.Colimit →+* StandardColimit :=
  directLimitLift ComplexMatrixStage.bond forwardCone forwardCone_compatible

@[simp] theorem toStandardColimit_stage
    (n : Nat) (A : ComplexMatrixStage.Stage n) :
    toStandardColimit (ComplexMatrixStage.toColimit n A) =
      standardToColimit n (stageStarAlgEquiv n A) := by
  rfl

/-- Stagewise inverse map back into the BitWord-indexed algebraic colimit. -/
def backwardCone (n : Nat) : StandardStage n →+* ComplexMatrixStage.Colimit :=
  (ComplexMatrixStage.toColimit n).comp
    (stageStarAlgEquiv n).symm.toRingEquiv.toRingHom

/-- The inverse stage maps form a compatible cone. -/
theorem backwardCone_compatible :
    CompatibleCone standardBond backwardCone := by
  intro n A
  change ComplexMatrixStage.toColimit (n + 1)
      ((stageStarAlgEquiv (n + 1)).symm (concreteStep n A)) =
    ComplexMatrixStage.toColimit n ((stageStarAlgEquiv n).symm A)
  have hbond := stageStarAlgEquiv_bond_hom n ((stageStarAlgEquiv n).symm A)
  simp only [StarAlgEquiv.apply_symm_apply] at hbond
  have hinv :
      (stageStarAlgEquiv (n + 1)).symm (concreteStep n A) =
        ComplexMatrixStage.bond n ((stageStarAlgEquiv n).symm A) := by
    rw [← hbond]
    exact (stageStarAlgEquiv (n + 1)).symm_apply_apply _
  rw [hinv]
  exact ComplexMatrixStage.toColimit_bond n ((stageStarAlgEquiv n).symm A)

/-- Global inverse homomorphism induced by the inverse stage equivalences. -/
noncomputable def fromStandardColimit :
    StandardColimit →+* ComplexMatrixStage.Colimit :=
  directLimitLift standardBond backwardCone backwardCone_compatible

@[simp] theorem fromStandardColimit_stage
    (n : Nat) (A : StandardStage n) :
    fromStandardColimit (standardToColimit n A) =
      ComplexMatrixStage.toColimit n ((stageStarAlgEquiv n).symm A) := by
  rfl

/-- The forward and inverse colimit maps are inverse on the BitWord colimit. -/
theorem from_to_id (X : ComplexMatrixStage.Colimit) :
    fromStandardColimit (toStandardColimit X) = X := by
  induction X using DirectLimit.induction with
  | _ n A =>
      change fromStandardColimit
        (toStandardColimit (ComplexMatrixStage.toColimit n A)) =
        ComplexMatrixStage.toColimit n A
      rw [toStandardColimit_stage, fromStandardColimit_stage]
      congr 1
      have hA : (stageStarAlgEquiv n).symm
          (BitWordComplexStageReindex.equiv n A) = A := by
        simpa only [stageStarAlgEquiv_apply] using
          (stageStarAlgEquiv n).symm_apply_apply A
      exact (stageStarAlgEquiv n).symm_apply_apply A

/-- The forward and inverse colimit maps are inverse on the standard colimit. -/
theorem to_from_id (X : StandardColimit) :
    toStandardColimit (fromStandardColimit X) = X := by
  induction X using DirectLimit.induction with
  | _ n A =>
      change toStandardColimit
        (fromStandardColimit (standardToColimit n A)) =
        standardToColimit n A
      rw [fromStandardColimit_stage, toStandardColimit_stage]
      simp

/-- Algebraic equivalence of the two naturally isomorphic complex dyadic towers. -/
noncomputable def colimitRingEquiv :
    ComplexMatrixStage.Colimit ≃+* StandardColimit where
  toFun := toStandardColimit
  invFun := fromStandardColimit
  left_inv := from_to_id
  right_inv := to_from_id
  map_add' := map_add toStandardColimit
  map_mul' := map_mul toStandardColimit

@[simp] theorem colimitRingEquiv_stage
    (n : Nat) (A : ComplexMatrixStage.Stage n) :
    colimitRingEquiv (ComplexMatrixStage.toColimit n A) =
      standardToColimit n (stageStarAlgEquiv n A) := by
  rfl

end InfoGeometry.Canonical.BitWordComplexStandardColimitEquivalence
