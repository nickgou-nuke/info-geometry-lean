import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics

namespace InfoGeometry.Physics

/-- The Sr-75 Nucleus (Z=38, N=37) -/
def Sr75 : Nucleus := (38, 37)

/-- The Rb-75 Nucleus (Z=37, N=38) -/
def Rb75 : Nucleus := (37, 38)

/-- The A=75 Mirror Pair (Sr-75 and Rb-75). -/
def A75Pair : MirrorPair :=
  ⟨(Sr75, Rb75), by
    constructor <;> rfl⟩

/-- Gamow-Teller decay properties for the A=75 mirror system (Huikari 2003). -/
abbrev GamowTellerDecay :=
  {data : ℝ × (ℝ × (ℝ × ℝ)) // |data.1 - 0.35| < 0.01}

namespace GamowTellerDecay

abbrev matrix_element_sigma_tau (D : GamowTellerDecay) : ℝ := D.1.1
abbrev approx_0_35 (D : GamowTellerDecay) :
    |D.matrix_element_sigma_tau - 0.35| < 0.01 := D.2
abbrev beta_delayed_proton_branching (D : GamowTellerDecay) : ℝ := D.1.2.1
abbrev high_lying_state_feeding (D : GamowTellerDecay) : ℝ := D.1.2.2.1
abbrev deformation (D : GamowTellerDecay) : ℝ := D.1.2.2.2

end GamowTellerDecay

/-- Formalizes the physical link found in Huikari 2003:
    In the A=75 mirror decay, strong nuclear deformation leads to
    significant β-decay feeding into high-lying excited states,
    which then decay by emitting a proton, yielding a large
    β-delayed proton branching. -/
theorem large_proton_branching_from_deformation (decay : GamowTellerDecay)
    (h_strong_deformation : decay.deformation > 0.3)
    (h_feeding_induced : decay.high_lying_state_feeding ≥ 10.0 * decay.deformation)
    (h_branching_induced : decay.beta_delayed_proton_branching ≥ 0.05 * decay.high_lying_state_feeding) :
    decay.beta_delayed_proton_branching > 0.15 := by
  nlinarith

end InfoGeometry.Physics
