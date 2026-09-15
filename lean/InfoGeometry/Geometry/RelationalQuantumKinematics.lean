import InfoGeometry.Geometry.ParticleReferenceFrames
import InfoGeometry.Geometry.CocyclicDressing

namespace InfoGeometry.Geometry.RelationalQuantumKinematics

open DressingField ParticleReferenceFrames CocyclicDressing
open InfoGeometry.Canonical.Algebraic

variable {Gauge Configuration : Type*} [Group Gauge] [MulAction Gauge Configuration]

noncomputable def actionWave (action : Configuration → ℝ) (hbar : ℝ) (amplitude : ℂ)
    (configuration : Configuration) : ℂ :=
  (Circle.exp (-action configuration / hbar) : ℂ) * amplitude

theorem actionWave_isCocyclic (action : Configuration → ℝ) (hbar : ℝ) (amplitude : ℂ) :
    IsCocyclic (actionPhase (Gauge := Gauge) action hbar) (actionWave action hbar amplitude) := by
  intro gauge configuration
  change (Circle.exp (-action (gauge • configuration) / hbar) : ℂ) * amplitude =
    ((Circle.exp (-action (gauge • configuration) / hbar) *
      (Circle.exp (-action configuration / hbar))⁻¹ : Circle) : ℂ) *
        ((Circle.exp (-action configuration / hbar) : ℂ) * amplitude)
  simp [mul_assoc]

theorem dressedWave_norm_change_frame (cocycle : MulActionCocycle Gauge Configuration Circle)
    (first second : Configuration →[Gauge] Gauge) (wave : Configuration → ℂ)
    (equivariant : IsCocyclic cocycle wave) (configuration : Configuration) :
    ‖dressedField second wave configuration‖ = ‖dressedField first wave configuration‖ := by
  rw [dressedField_change_frame cocycle first second wave equivariant configuration]
  exact Circle.norm_smul _ _

theorem actionWave_frame_change (action : Configuration → ℝ) (hbar : ℝ) (amplitude : ℂ)
    (first second : Configuration →[Gauge] Gauge) (configuration : Configuration) :
    dressedField second (actionWave action hbar amplitude) configuration =
      Circle.exp (-(action (normalize second configuration) -
        action (normalize first configuration)) / hbar) •
          dressedField first (actionWave action hbar amplitude) configuration := by
  rw [dressedField_change_frame (actionPhase action hbar) first second _
    (actionWave_isCocyclic action hbar amplitude), frameTransport_actionPhase]

section ParticleFrames

variable {Particle Position : Type*} [AddCommGroup Position]

theorem particle_dressedField (reference : Particle) (wave : (Particle → Position) → ℂ)
    (positions : Particle → Position) :
    dressedField (particleFrame reference) wave positions = wave (relative reference positions) := by
  rw [relative_eq_normalize]
  rfl

theorem particle_frame_covariance
    (cocycle : MulActionCocycle (Multiplicative Position) (Particle → Position) Circle)
    (wave : (Particle → Position) → ℂ) (equivariant : IsCocyclic cocycle wave)
    (first second : Particle) (positions : Particle → Position) :
    wave (relative second positions) =
      frameTransport cocycle (particleFrame first) (particleFrame second) positions •
        wave (relative first positions) ∧
    ‖wave (relative second positions)‖ = ‖wave (relative first positions)‖ := by
  constructor
  · simpa only [particle_dressedField] using dressedField_change_frame cocycle
      (particleFrame first) (particleFrame second) wave equivariant positions
  · simpa only [particle_dressedField] using dressedWave_norm_change_frame cocycle
      (particleFrame first) (particleFrame second) wave equivariant positions

end ParticleFrames

end InfoGeometry.Geometry.RelationalQuantumKinematics
