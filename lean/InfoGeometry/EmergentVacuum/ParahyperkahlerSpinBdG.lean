import InfoGeometry.Quantum.AnticommutingInvolutionCore
import InfoGeometry.QuantumContext.MassAsCommutantCoupling
import InfoGeometry.SuperMetriplectic.Flow

namespace InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG

structure SplitQuaternionPair (Carrier : Type*) [Ring Carrier] where
  elliptic : Carrier
  split : Carrier
  elliptic_sq : elliptic * elliptic = -1
  split_sq : split * split = 1
  anticommute : elliptic * split = -(split * elliptic)

namespace SplitQuaternionPair

variable {Carrier : Type*} [Ring Carrier]

def third (axes : SplitQuaternionPair Carrier) : Carrier := axes.elliptic * axes.split

theorem swap (axes : SplitQuaternionPair Carrier) :
    axes.split * axes.elliptic = -(axes.elliptic * axes.split) := by
  simpa using (congrArg Neg.neg axes.anticommute).symm

theorem third_sq (axes : SplitQuaternionPair Carrier) : axes.third * axes.third = 1 := by
  unfold third
  calc
    (axes.elliptic * axes.split) * (axes.elliptic * axes.split) =
        axes.elliptic * (axes.split * axes.elliptic) * axes.split := by noncomm_ring
    _ = axes.elliptic * (-(axes.elliptic * axes.split)) * axes.split := by rw [axes.swap]
    _ = -(axes.elliptic * axes.elliptic) * (axes.split * axes.split) := by noncomm_ring
    _ = 1 := by rw [axes.elliptic_sq, axes.split_sq]; simp

noncomputable def ofInvolutionCore (core : InfoGeometry.Quantum.AnticommutingInvolutionCore) :
    SplitQuaternionPair (Module.End ℝ core) where
  elliptic := core.K
  split := core.J
  elliptic_sq := core.K_sq
  split_sq := core.J_sq
  anticommute := by
    change core.K.comp core.J = -(core.J.comp core.K)
    rw [core.k_comp_j, core.j_comp_k]

end SplitQuaternionPair

theorem equilibrium_reduction {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
    (flow : InfoGeometry.SuperMetriplectic.MetriplecticFlow Space)
    (equilibrium : flow.IsDissipativeEquilibrium) :
    flow.totalFlow = flow.reversibleFlow ∧ flow.dissipativeFlow = 0 ∧
      flow.entropyProduction = 0 := by
  have zeroFlow := flow.dissipativeFlow_eq_zero_of_equilibrium equilibrium
  refine ⟨?_, zeroFlow, ?_⟩
  · rw [flow.totalFlow_eq_reversible_add_dissipative, zeroFlow, add_zero]
  · rw [flow.entropyProduction_eq_quadratic, zeroFlow]
    exact flow.metric.pairing_zero_right flow.entropyForce

theorem scalar_square_of_anticommutation {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]
    (kinetic coupling : Carrier) (kineticSquared couplingSquared : ℝ)
    (anticommute : kinetic * coupling + coupling * kinetic = 0)
    (kineticSquare : kinetic * kinetic = algebraMap ℝ Carrier kineticSquared)
    (couplingSquare : coupling * coupling = algebraMap ℝ Carrier couplingSquared) :
    (kinetic + coupling) * (kinetic + coupling) =
      algebraMap ℝ Carrier (kineticSquared + couplingSquared) := by
  rw [InfoGeometry.QuantumContext.MassAsCommutantCoupling.square_sum_of_anticommute
    kinetic coupling anticommute, kineticSquare, couplingSquare, map_add]

end InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdG
