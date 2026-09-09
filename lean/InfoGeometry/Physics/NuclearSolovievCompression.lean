import Mathlib
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

/-!
# Compatibility surface for the canonical Soloviev compression

The former owner duplicated an obsolete real `Sheet`/`Carrier` model.  The
canonical implementation is the native complex common carrier in
`NuclearFiveGradeSolovievCommonCompression`.  This module preserves the old
public names as transparent aliases and forwards its theorems to that owner.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSolovievCompression

open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev ModelVector := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.ModelVector
abbrev Carrier := InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.Carrier
abbrev Operator := InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.Operator

abbrev modelEmbed := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelEmbed
abbrev modelReadout := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelReadout
abbrev modelProjection := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelProjection
abbrev fullQPNMHamiltonian := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.fullHamiltonian
abbrev compressedAction := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.compressedAction

theorem modelReadout_modelEmbed (v : ModelVector) :
    modelReadout (modelEmbed v) = v :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelReadout_modelEmbed v

theorem modelProjection_idempotent :
    modelProjection * modelProjection = modelProjection :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelProjection_idempotent

theorem compressedAction_zero (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.compressedAction_zero
    Eqp omega V C D

theorem compressedAction_one (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] 1 =
      V * C + (Eqp + omega) * D :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.compressedAction_one
    Eqp omega V C D

theorem compressedAction_eq_qpnm_mulVec (Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
      Matrix.mulVec (qpnmMatrix Eqp omega V) ![C, D] :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.compressedAction_eq_qpnm_mulVec
    Eqp omega V C D

theorem compressed_eigenvalue_system (Eqp omega V E C D : ℝ) :
    compressedAction Eqp omega V ![C, D] = E • ![C, D] ↔
      ((Eqp - E) * C + V * D = 0 ∧
        V * C + (Eqp + omega - E) * D = 0) := by
  rw [compressedAction_eq_qpnm_mulVec]
  exact qpnm_eigenvalue_system Eqp omega V E C D

theorem soloviev_compression_packet (Eqp omega V C D : ℝ) :
    modelReadout (modelEmbed ![C, D]) = ![C, D] ∧
      compressedAction Eqp omega V ![C, D] =
        Matrix.mulVec (qpnmMatrix Eqp omega V) ![C, D] ∧
      compressedAction Eqp omega V ![C, D] 0 = Eqp * C + V * D ∧
      compressedAction Eqp omega V ![C, D] 1 =
        V * C + (Eqp + omega) * D := by
  exact ⟨modelReadout_modelEmbed _,
    compressedAction_eq_qpnm_mulVec Eqp omega V C D,
    compressedAction_zero Eqp omega V C D,
    compressedAction_one Eqp omega V C D⟩

end InfoGeometry.Physics.NuclearSolovievCompression
