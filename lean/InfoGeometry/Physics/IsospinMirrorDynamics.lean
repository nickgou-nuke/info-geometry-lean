import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Physics

/-!
# Isospin Dynamics and Mirror Nuclei
Formalization of Isospin (SU(2)), Nucleons, Mirror Pairs, Mirror Energy Difference (MED),
Transition Rates, Thomas-Ehrman shift, Effective Charges, and Symmetry Energy correlation.
-/

/-- Isospin representation for a state, characterized by total isospin T and projection T_z. -/
structure Isospin where
  T : ℚ
  T_z : ℚ
  valid : |T_z| ≤ T
  integer_step : ∃ (n : ℕ), T - T_z = n

/-- Nucleon type, either proton or neutron. -/
inductive Nucleon
  | proton
  | neutron
  deriving Repr, DecidableEq

/-- The isospin projection T_z of a nucleon. -/
def Nucleon.T_z (n : Nucleon) : ℚ :=
  match n with
  | .proton => 1 / 2
  | .neutron => - (1 / 2)

/-- A nucleus defined by its proton number Z and neutron number N. -/
structure Nucleus where
  Z : ℕ
  N : ℕ

/-- Mass number A of a nucleus. -/
def Nucleus.A (nuc : Nucleus) : ℕ := nuc.Z + nuc.N

/-- A Mirror Pair of nuclei, where (Z1, N1) = (N2, Z2). -/
structure MirrorPair where
  nuc1 : Nucleus
  nuc2 : Nucleus
  mirror_cond_Z : nuc1.Z = nuc2.N
  mirror_cond_N : nuc1.N = nuc2.Z

/-- Mass number of the mirror pair. -/
def MirrorPair.A (mp : MirrorPair) : ℕ := mp.nuc1.A

/-- Mirror Energy Difference (MED).
  The difference in excitation energy between analogue states in a mirror pair. -/
def MED (E_exc1 E_exc2 : ℝ) : ℝ :=
  E_exc1 - E_exc2

/-- Electromagnetic transition rate B(Eλ). -/
structure TransitionRate (lambda : ℕ) where
  rate : ℝ
  rate_nonneg : 0 ≤ rate

/-- Nuclear State characterizing a level. -/
structure NuclearState where
  energy : ℝ
  spin : ℚ
  parity : ℤ
  isospin : Isospin
  l : ℕ -- orbital angular momentum

/-- Thomas-Ehrman shift observable: proton-rich minus neutron-rich analogue energy. -/
def thomasEhrmanEnergyShift
    (state_Z_greater state_N_greater : NuclearState) : ℝ :=
  state_Z_greater.energy - state_N_greater.energy

/--
The Thomas-Ehrman positivity claim is a condition on the chosen energy data.
The isospin, proton-rich, s-wave, and analogue hypotheses identify the physical
lane; they do not determine an energy inequality by themselves.
-/
theorem thomas_ehrman_shift
    (state_Z_greater state_N_greater : NuclearState)
    (_h_mirror : state_Z_greater.isospin.T_z = - state_N_greater.isospin.T_z)
    (_h_proton_rich : state_Z_greater.isospin.T_z > 0)
    (_h_swave : state_Z_greater.l = 0)
    (_h_analogue : state_Z_greater.spin = state_N_greater.spin ∧
      state_Z_greater.parity = state_N_greater.parity) :
    0 < thomasEhrmanEnergyShift state_Z_greater state_N_greater ↔
      state_Z_greater.energy - state_N_greater.energy > 0 := by
  rfl

/-- Effective charges for protons and neutrons in a given model space. -/
structure EffectiveCharge where
  e_pi : ℝ -- effective proton charge
  e_nu : ℝ -- effective neutron charge

/-- Symmetry Energy parameters. -/
structure EquationOfState where
  S_0 : ℝ -- Symmetry energy at saturation density
  L : ℝ   -- Slope parameter of the symmetry energy

/-- A model for the charge radius difference of mirror nuclei. -/
structure ChargeRadiusDifference where
  delta_R_ch : ℝ

/-- The correlation between the slope of the symmetry energy L and the difference
  in charge radii of mirror nuclei (ΔR_ch). Often formulated as a linear correlation. -/
def symmetry_energy_L_correlation (eos : EquationOfState) (radius_diff : ChargeRadiusDifference) : Prop :=
  ∃ (a b : ℝ), a > 0 ∧ radius_diff.delta_R_ch = a * eos.L + b

end InfoGeometry.Physics
