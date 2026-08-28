import Mathlib

namespace InfoGeometry.Physics.NuclearChiralPRM

/-! A finite algebraic chiral-doublet readout.  The parameters are explicit;
no particle--rotor Hamiltonian or physical projector identification is assumed. -/

structure TriaxialMoments where
  J_s : ℝ
  J_m : ℝ
  J_l : ℝ
  pos_s : 0 < J_s
  pos_m : 0 < J_m
  pos_l : 0 < J_l
  intermediate_dominant : J_s < J_m ∧ J_l < J_m

structure ChiralDoubletState where
  E_diag : ℝ
  Delta : ℝ

def energyPlus (state : ChiralDoubletState) : ℝ :=
  state.E_diag - state.Delta

def energyMinus (state : ChiralDoubletState) : ℝ :=
  state.E_diag + state.Delta

theorem chiral_doublet_energy_splitting (state : ChiralDoubletState) :
    energyMinus state - energyPlus state = 2 * state.Delta := by
  dsimp [energyMinus, energyPlus]
  ring

theorem chiral_static_degeneracy (state : ChiralDoubletState)
    (h_tunnel : state.Delta = 0) :
    energyPlus state = energyMinus state := by
  dsimp [energyPlus, energyMinus]
  rw [h_tunnel]
  simp

end InfoGeometry.Physics.NuclearChiralPRM
