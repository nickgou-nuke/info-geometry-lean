import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
import InfoGeometry.Clifford.Cl55SpinorVolumeOddTransport

/-!
# Predicate readback for the matrix chiral sectors

The sector submodules and the native chirality predicates are two views of the
same projector equations.  This file records that readback without asserting
any octonionic model or a dimension statement.
-/

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

theorem mem_chiralPlusSector_iff_chiralPlus (v : SpinorSpace 5) :
    v ∈ chiralPlusSector ↔ chiralPlus v := by
  exact (chiralPlus_iff_projector_fixed v).symm

theorem mem_chiralMinusSector_iff_chiralMinus (v : SpinorSpace 5) :
    v ∈ chiralMinusSector ↔ chiralMinus v := by
  exact (chiralMinus_iff_projector_fixed v).symm

theorem mem_chiralPlusSector_iff_volume_eigenvalue (v : SpinorSpace 5) :
    v ∈ chiralPlusSector ↔
      matrixApply chiralityMatrix v = v := by
  exact mem_chiralPlusSector_iff_chiralPlus v

theorem mem_chiralMinusSector_iff_volume_eigenvalue (v : SpinorSpace 5) :
    v ∈ chiralMinusSector ↔
      matrixApply chiralityMatrix v = -v := by
  exact mem_chiralMinusSector_iff_chiralMinus v

theorem odd_action_maps_plus_to_minus
    (M : SpinorMatrix 5)
    (hM : M * chiralityMatrix = -(chiralityMatrix * M))
    (v : SpinorSpace 5) (hv : chiralPlus v) :
    chiralMinus (matrixApply M v) := by
  have hM' : chiralityMatrix * M = -(M * chiralityMatrix) := by
    rw [hM]
    module
  change matrixApply chiralityMatrix (matrixApply M v) =
    -matrixApply M v
  rw [← matrixApply_mul, hM', matrixApply_neg, matrixApply_mul, hv]

theorem odd_action_maps_minus_to_plus
    (M : SpinorMatrix 5)
    (hM : M * chiralityMatrix = -(chiralityMatrix * M))
    (v : SpinorSpace 5) (hv : chiralMinus v) :
    chiralPlus (matrixApply M v) := by
  have hM' : chiralityMatrix * M = -(M * chiralityMatrix) := by
    rw [hM]
    module
  change matrixApply chiralityMatrix (matrixApply M v) =
    matrixApply M v
  rw [← matrixApply_mul, hM', matrixApply_neg, matrixApply_mul, hv]
  have hneg : matrixApply M (-v) = -matrixApply M v := by
    rw [matrixApply_eq_mulVec, matrixApply_eq_mulVec]
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [hneg]
  module

theorem cl55_odd_generator_maps_plus_to_minus
    (a : V55) (v : SpinorSpace 5) (hv : chiralPlus v) :
    chiralMinus
      (matrixApply (cl55SpinorAlgEquiv (ι55 a)) v) := by
  exact odd_action_maps_plus_to_minus
    (cl55SpinorAlgEquiv (ι55 a))
    (spinor_chirality_anticommutes_vector a) v hv

theorem cl55_odd_generator_maps_minus_to_plus
    (a : V55) (v : SpinorSpace 5) (hv : chiralMinus v) :
    chiralPlus
      (matrixApply (cl55SpinorAlgEquiv (ι55 a)) v) := by
  exact odd_action_maps_minus_to_plus
    (cl55SpinorAlgEquiv (ι55 a))
    (spinor_chirality_anticommutes_vector a) v hv

theorem cl55_odd_generator_maps_plusSector_to_minusSector
    (a : V55) (v : chiralPlusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 ∈
      chiralMinusSector := by
  rw [mem_chiralMinusSector_iff_chiralMinus]
  apply cl55_odd_generator_maps_plus_to_minus a v.1
  exact (mem_chiralPlusSector_iff_chiralPlus v.1).mp v.2

theorem cl55_odd_generator_maps_minusSector_to_plusSector
    (a : V55) (v : chiralMinusSector) :
    Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 ∈
      chiralPlusSector := by
  rw [mem_chiralPlusSector_iff_chiralPlus]
  apply cl55_odd_generator_maps_minus_to_plus a v.1
  exact (mem_chiralMinusSector_iff_chiralMinus v.1).mp v.2

noncomputable def cl55OddGeneratorPlusToMinus (a : V55) :
    chiralPlusSector →ₗ[ℝ] chiralMinusSector where
  toFun v := ⟨Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1,
    cl55_odd_generator_maps_plusSector_to_minusSector a v⟩
  map_add' v w := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (v.1 + w.1) =
      Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 +
        Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) w.1
    rw [Matrix.mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (c • v.1) =
      c • Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1
    rw [Matrix.mulVec_smul]

noncomputable def cl55OddGeneratorMinusToPlus (a : V55) :
    chiralMinusSector →ₗ[ℝ] chiralPlusSector where
  toFun v := ⟨Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1,
    cl55_odd_generator_maps_minusSector_to_plusSector a v⟩
  map_add' v w := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (v.1 + w.1) =
      Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1 +
        Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) w.1
    rw [Matrix.mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    change Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) (c • v.1) =
      c • Matrix.mulVec (cl55SpinorAlgEquiv (ι55 a)) v.1
    rw [Matrix.mulVec_smul]

end InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
