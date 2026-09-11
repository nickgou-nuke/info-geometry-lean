import InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11BitWordRingColimitPeirceBridge
import InfoGeometry.Canonical.GNSCARColimit

/-!
# Clifford colimit to Cuntz/Cantor readout

This owner records the one-way horizontal map already supplied by
`CompatibleCuntzRepresentation`.  The Clifford tensor-tower colimit is the
source; a chosen Cuntz representation is the target.  The BitWord/UHF
equivalence is used only to transport finite matrix/core-unit readouts.

No Cuntz structure is imposed on the UHF colimit, and no Fock identification
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BitWordCuntzCantorBridge

open InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
open InfoGeometry.Canonical.Cl11BitWordRingColimitPeirceBridge
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Canonical.GNSCARColimit

variable {Op : Type} [Ring Op] [StarRing Op]

variable (R : CompatibleCuntzRepresentation (Op := Op))

def uhfStageMap (n : ℕ) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n →+* Op :=
  R.stageMap n |>.comp (clStageEquiv n).symm.toRingHom

theorem uhfStageMap_compatible
    (n : ℕ) (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n) :
    uhfStageMap R (n + 1)
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n A) =
      uhfStageMap R n A := by
  change R.stageMap (n + 1)
      ((clStageEquiv (n + 1)).symm
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n A)) =
    R.stageMap n ((clStageEquiv n).symm A)
  rw [show (clStageEquiv (n + 1)).symm
        (InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n A) =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond n
        ((clStageEquiv n).symm A) by
    apply (clStageEquiv (n + 1)).injective
    rw [clStageEquiv_bond]
    simp]
  exact R.stage_compat n ((clStageEquiv n).symm A)

noncomputable def uhfCarrierRepresentation :
    InfoGeometry.Algebra.PrimonColimitAlgebra.PrimonUHFAlgebra →+* Op :=
  CompatibleCuntzRepresentation.representation R |>.comp uhfToCl

theorem uhfCarrierRepresentation_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n) :
    uhfCarrierRepresentation R
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n A) =
      uhfStageMap R n A := by
  change CompatibleCuntzRepresentation.representation R
      (uhfToCl (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n A)) = _
  rw [uhfToCl_toColimit]
  change CompatibleCuntzRepresentation.representation R
      (ofStage n ((clStageEquiv n).symm A)) =
    R.stageMap n ((clStageEquiv n).symm A)
  exact CompatibleCuntzRepresentation.representation_stage R n
    ((clStageEquiv n).symm A)

theorem uhfCarrierRepresentation_peircePlusMinus_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage (n + 1)) :
    uhfCarrierRepresentation R
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (n + 1)
          (bitWordPeircePlusMinus n A)) =
      uhfStageMap R (n + 1) (bitWordPeircePlusMinus n A) := by
  exact uhfCarrierRepresentation_stage R (n + 1)
    (bitWordPeircePlusMinus n A)

theorem uhfCarrierRepresentation_peirceMinusPlus_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage (n + 1)) :
    uhfCarrierRepresentation R
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (n + 1)
          (bitWordPeirceMinusPlus n A)) =
      uhfStageMap R (n + 1) (bitWordPeirceMinusPlus n A) := by
  exact uhfCarrierRepresentation_stage R (n + 1)
    (bitWordPeirceMinusPlus n A)

theorem uhfCarrierRepresentation_peircePlusPlus_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage (n + 1)) :
    uhfCarrierRepresentation R
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (n + 1)
          (bitWordPeircePlusPlus n A)) =
      uhfStageMap R (n + 1) (bitWordPeircePlusPlus n A) := by
  exact uhfCarrierRepresentation_stage R (n + 1)
    (bitWordPeircePlusPlus n A)

theorem uhfCarrierRepresentation_peirceMinusMinus_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage (n + 1)) :
    uhfCarrierRepresentation R
        (InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit (n + 1)
          (bitWordPeirceMinusMinus n A)) =
      uhfStageMap R (n + 1) (bitWordPeirceMinusMinus n A) := by
  exact uhfCarrierRepresentation_stage R (n + 1)
    (bitWordPeirceMinusMinus n A)

theorem representation_clifford_stage (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    CompatibleCuntzRepresentation.representation R
        (ofStage n A) = R.stageMap n A := by
  exact CompatibleCuntzRepresentation.representation_stage R n A

theorem representation_limit_car_generators (k : ℕ) :
    CompatibleCuntzRepresentation.representation R (limit_u k) =
        R.stageMap (k + 1) (jw_u_new k) ∧
      CompatibleCuntzRepresentation.representation R (limit_v k) =
        R.stageMap (k + 1) (jw_v_new k) := by
  constructor
  · exact CompatibleCuntzRepresentation.representation_stage R (k + 1)
      (jw_u_new k)
  · exact CompatibleCuntzRepresentation.representation_stage R (k + 1)
      (jw_v_new k)

/-! The chosen Cuntz readout preserves the algebraic CAR laws of the
    Clifford-colimit representatives.  These are readout theorems only: no
    injectivity or Cuntz--CAR equivalence is asserted. -/

theorem representation_limit_creation_sq_zero (k : ℕ) :
    CompatibleCuntzRepresentation.representation R (limit_u k) *
        CompatibleCuntzRepresentation.representation R (limit_u k) = 0 := by
  rw [← map_mul, limit_u_sq_zero, map_zero]

theorem representation_limit_annihilation_sq_zero (k : ℕ) :
    CompatibleCuntzRepresentation.representation R (limit_v k) *
        CompatibleCuntzRepresentation.representation R (limit_v k) = 0 := by
  rw [← map_mul, limit_v_sq_zero, map_zero]

theorem representation_limit_car_anticommutator (k : ℕ) :
    CompatibleCuntzRepresentation.representation R (limit_u k) *
          CompatibleCuntzRepresentation.representation R (limit_v k) +
        CompatibleCuntzRepresentation.representation R (limit_v k) *
          CompatibleCuntzRepresentation.representation R (limit_u k) = 1 := by
  rw [← map_mul, ← map_mul, ← map_add, limit_uv_anticomm, map_one]

theorem representation_uhf_stage (n : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage n) :
    CompatibleCuntzRepresentation.representation R
        (ofStage n ((clStageEquiv n).symm A)) =
      R.stageMap n ((clStageEquiv n).symm A) := by
  exact representation_clifford_stage R n ((clStageEquiv n).symm A)

theorem representation_uhf_core_unit (n : ℕ)
    (u v : InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n) :
    CompatibleCuntzRepresentation.representation R
        (ofStage n (cl11CuntzCoreUnit n u v)) =
      R.stageMap n (cl11CuntzCoreUnit n u v) := by
  exact representation_clifford_stage R n (cl11CuntzCoreUnit n u v)

theorem representation_clifford_finiteAdvance (m k : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage m) :
    CompatibleCuntzRepresentation.representation R
        (intoCarrier (m + k) (finiteAdvance m k A)) =
      R.stageMap m A := by
  exact CompatibleCuntzRepresentation.representation_finiteAdvance R m k A

theorem representation_uhf_finiteAdvance (m k : ℕ)
    (A : InfoGeometry.Algebra.PrimonColimitAlgebra.MatrixStage m) :
    CompatibleCuntzRepresentation.representation R
        (intoCarrier (m + k)
          (finiteAdvance m k ((clStageEquiv m).symm A))) =
      R.stageMap m ((clStageEquiv m).symm A) := by
  exact representation_clifford_finiteAdvance R m k ((clStageEquiv m).symm A)

theorem representation_cantorOrbit_branch (b : Bool) (w : List Bool) :
    CompatibleCuntzRepresentation.cantorOrbit R (b :: w) =
      (if b then InfoGeometry.Topology.CuntzO2Carrier.S_right R.cuntz
      else InfoGeometry.Topology.CuntzO2Carrier.S_left R.cuntz) *
        CompatibleCuntzRepresentation.cantorOrbit R w := by
  exact CompatibleCuntzRepresentation.cantorOrbit_branch R b w

end InfoGeometry.Canonical.Cl11BitWordCuntzCantorBridge
