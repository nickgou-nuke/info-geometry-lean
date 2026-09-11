import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

/-! Canonical projected-Hamiltonian interface for the common CAR--CCR carrier. -/
noncomputable section
namespace InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.SolovievQPNMEigenproblem
abbrev ModelVector := InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.ModelVector
abbrev Carrier := InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.Carrier
abbrev Operator := InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.Operator
abbrev modelProjection : Operator :=
  InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelProjection
@[simp] theorem modelProjection_idempotent :
    modelProjection * modelProjection = modelProjection := by
  exact InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression.modelProjection_idempotent
theorem projectedHamiltonian_on_model (Eqp omega V : ℝ) (v : ModelVector) :
    modelProjection ((fullHamiltonian Eqp omega V) (modelEmbed v)) =
      modelEmbed (compressedAction Eqp omega V v) := by
  rfl

theorem projected_soloviev_packet (Eqp omega V C D : ℝ) :
    modelProjection * modelProjection = modelProjection ∧
      modelProjection (modelEmbed ![C, D]) = modelEmbed ![C, D] ∧
      modelProjection
          (fullHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C, D]))) =
        modelEmbed (Matrix.mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  exact ⟨modelProjection_idempotent,
    modelProjection_modelEmbed _,
    projected_fullHamiltonian_on_model Eqp omega V C D⟩

theorem projected_fullQPNM_on_model (Eqp omega V C D : ℝ) :
    modelProjection
        (fullHamiltonian Eqp omega V
          (modelProjection (modelEmbed ![C, D]))) =
      modelEmbed (Matrix.mulVec (qpnmMatrix Eqp omega V) ![C, D]) :=
  projected_fullHamiltonian_on_model Eqp omega V C D
end InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
