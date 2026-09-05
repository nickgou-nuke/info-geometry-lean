import InfoGeometry.Physics.NuclearSolovievCompression

/-!
# Idempotent model-space projection for the Soloviev compression

The section `modelEmbed` and retraction `modelReadout` determine the projection
`P = modelEmbed ∘ modelReadout` on the common quasiparticle--phonon carrier.
This file proves `P²=P` and the exact projected-Hamiltonian relation

`P H_full P (embed v) = embed (H_QPNM *ᵥ v)`.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian

open Matrix
open InfoGeometry.Physics.NuclearCARPhononCommonCarrier
open InfoGeometry.Physics.NuclearSolovievCompression
open InfoGeometry.Physics.SolovievQPNMEigenproblem

/-- Projection onto the selected zero/one-phonon occupied quasiparticle
channels. -/
def modelProjection : Operator :=
  modelEmbed.comp modelReadout

@[simp] theorem modelProjection_apply (ψ : Carrier) :
    modelProjection ψ = modelEmbed (modelReadout ψ) := rfl

/-- The section is fixed by the projection. -/
@[simp] theorem modelProjection_modelEmbed (v : ModelVector) :
    modelProjection (modelEmbed v) = modelEmbed v := by
  rw [modelProjection_apply, modelReadout_modelEmbed]

/-- The model-space map is idempotent. -/
theorem modelProjection_idempotent :
    modelProjection * modelProjection = modelProjection := by
  apply LinearMap.ext
  intro ψ
  rw [Module.End.mul_apply, modelProjection_apply,
    modelProjection_apply, modelProjection_modelEmbed]

/-- Projected full Hamiltonian on an embedded model vector. -/
theorem projected_fullQPNM_on_model
    (Eqp omega V C D : ℝ) :
    modelProjection
        (fullQPNMHamiltonian Eqp omega V
          (modelProjection (modelEmbed ![C, D]))) =
      modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  rw [modelProjection_modelEmbed, modelProjection_apply]
  change modelEmbed (compressedAction Eqp omega V ![C, D]) = _
  rw [compressedAction_eq_qpnm_mulVec]

/-- Endomorphism form of the projected model action after applying the
retraction. -/
theorem readout_projected_fullQPNM
    (Eqp omega V C D : ℝ) :
    modelReadout
        (modelProjection
          (fullQPNMHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C, D])))) =
      mulVec (qpnmMatrix Eqp omega V) ![C, D] := by
  rw [projected_fullQPNM_on_model, modelReadout_modelEmbed]

/-- Exact `P H P` closure packet. -/
theorem projected_soloviev_packet
    (Eqp omega V C D : ℝ) :
    modelProjection * modelProjection = modelProjection ∧
      modelProjection (modelEmbed ![C, D]) = modelEmbed ![C, D] ∧
      modelProjection
          (fullQPNMHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C, D]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  exact ⟨modelProjection_idempotent,
    modelProjection_modelEmbed _,
    projected_fullQPNM_on_model Eqp omega V C D⟩

end InfoGeometry.Physics.NuclearSolovievProjectedHamiltonian
