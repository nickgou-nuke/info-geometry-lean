import InfoGeometry.Geometry.RelationalQuantumDependency

namespace InfoGeometry.Geometry.RelationalQuantumKinematics.Tests

open DressingField ParticleReferenceFrames CocyclicDressing
open InfoGeometry.Canonical.Algebraic

example : relative (1 : Fin 3) ![(2 : ℤ), 5, 9] = ![-3, 0, 4] := by
  decide

example : relative (1 : Fin 3) ![(12 : ℤ), 15, 19] =
    relative (1 : Fin 3) ![(2 : ℤ), 5, 9] := by
  decide

example : relative (0 : Fin 3) ![(2 : ℤ), 6, 9] ≠
    relative (0 : Fin 3) ![(2 : ℤ), 5, 9] := by
  decide

example {Time Particle Position : Type*} [AddCommGroup Position]
    (reference : Particle) (history : Time → Particle → Position) (shift : Time → Position) :
    (fun time => relative reference (fun particle => shift time + history time particle)) =
      fun time => relative reference (history time) :=
  relative_history_invariant reference history shift

example : actionPhase (Gauge := Multiplicative ℝ) (fun position : ℝ => position ^ 2) 1
    (Multiplicative.ofAdd 1) 1 = Circle.exp (-3) := by
  rw [actionPhase_apply]
  change Circle.exp (-(((1 : ℝ) + 1) ^ 2 - 1 ^ 2) / 1) = Circle.exp (-3)
  norm_num

example : frameTransport (actionPhase (Gauge := Multiplicative ℝ)
    (fun positions : Fin 3 → ℝ => (positions 0) ^ 2) 1)
    (particleFrame 0) (particleFrame 1) ![2, 5, 9] = Circle.exp (-9) := by
  rw [frameTransport_actionPhase, ← relative_eq_normalize, ← relative_eq_normalize]
  norm_num [relative]

example {Particle Position : Type*} [AddCommGroup Position]
    (action : (Particle → Position) → ℝ) (hbar : ℝ) (amplitude : ℂ)
    (first second : Particle) (positions : Particle → Position) :
    ‖actionWave action hbar amplitude (relative second positions)‖ =
      ‖actionWave action hbar amplitude (relative first positions)‖ :=
  (particle_frame_covariance (actionPhase action hbar) _
    (actionWave_isCocyclic action hbar amplitude) first second positions).2

example {Gauge Configuration Coefficient : Type*} [Group Gauge]
    [MulAction Gauge Configuration] [Group Coefficient]
    (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (first second third : Configuration →[Gauge] Gauge) (configuration : Configuration) :
    frameTransport cocycle second third configuration *
      frameTransport cocycle first second configuration =
        frameTransport cocycle first third configuration :=
  frameTransport_comp cocycle first second third configuration

#print axioms relative_eq_normalize
#print axioms relative_reference
#print axioms relative_translate
#print axioms relative_change_reference
#print axioms relative_preserves_difference
#print axioms relative_eq_iff_translation
#print axioms relative_history_invariant
#print axioms dressedField_invariant
#print axioms dressedField_formula
#print axioms normalize_change_frame
#print axioms dressedField_change_frame
#print axioms frameTransport_self
#print axioms frameTransport_comp
#print axioms frameTransport_invariant
#print axioms actionPhase_apply
#print axioms frameTransport_actionPhase
#print axioms frameTransport_preserves_norm
#print axioms actionWave_isCocyclic
#print axioms dressedWave_norm_change_frame
#print axioms actionWave_frame_change
#print axioms particle_dressedField
#print axioms particle_frame_covariance
#print axioms ProofDependency.causal_branches
#print axioms ProofDependency.normalization_and_cocycle_incomparable
#print axioms ProofDependency.no_dependency_cycle

end InfoGeometry.Geometry.RelationalQuantumKinematics.Tests
