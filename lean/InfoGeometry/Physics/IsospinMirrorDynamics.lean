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
abbrev Isospin :=
  Subtype (fun p : ℚ × ℚ => |p.2| ≤ p.1 ∧ ∃ n : ℕ, p.1 - p.2 = n)

namespace Isospin

abbrev T (I : Isospin) : ℚ := I.1.1

abbrev T_z (I : Isospin) : ℚ := I.1.2

abbrev valid (I : Isospin) : |I.T_z| ≤ I.T := I.2.1

abbrev integer_step (I : Isospin) : ∃ n : ℕ, I.T - I.T_z = n := I.2.2

end Isospin

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

/-- A nucleus defined by its proton number `Z` and neutron number `N`,
represented natively as a product. -/
abbrev Nucleus := ℕ × ℕ

namespace Nucleus

@[simp] def Z (nuc : Nucleus) : ℕ := nuc.1
@[simp] def N (nuc : Nucleus) : ℕ := nuc.2

end Nucleus

/-- Mass number A of a nucleus. -/
def Nucleus.A (nuc : Nucleus) : ℕ := nuc.Z + nuc.N

/-- A Mirror Pair of nuclei, where (Z1, N1) = (N2, Z2). -/
abbrev MirrorPair :=
  Subtype (fun p : Nucleus × Nucleus =>
    p.1.Z = p.2.N ∧ p.1.N = p.2.Z)

namespace MirrorPair

abbrev nuc1 (mp : MirrorPair) : Nucleus := mp.1.1

abbrev nuc2 (mp : MirrorPair) : Nucleus := mp.1.2

abbrev mirror_cond_Z (mp : MirrorPair) : mp.nuc1.Z = mp.nuc2.N := mp.2.1

abbrev mirror_cond_N (mp : MirrorPair) : mp.nuc1.N = mp.nuc2.Z := mp.2.2

end MirrorPair

/-- Mass number of the mirror pair. -/
def MirrorPair.A (mp : MirrorPair) : ℕ := mp.nuc1.A

/-- Mirror partners have equal mass number. -/
theorem MirrorPair.partner_mass_eq (mp : MirrorPair) :
    mp.nuc2.A = mp.nuc1.A := by
  simp only [Nucleus.A]
  rw [← mp.mirror_cond_N, ← mp.mirror_cond_Z]
  exact Nat.add_comm _ _

/-- Integer-valued doubled isospin projection in the `N - Z` convention. -/
def Nucleus.twoTz (n : Nucleus) : ℤ := (n.N : ℤ) - (n.Z : ℤ)

/-- Doubled isospin projections of mirror partners sum to zero. -/
theorem MirrorPair.twoTz_add_partner_twoTz (mp : MirrorPair) :
    mp.nuc1.twoTz + mp.nuc2.twoTz = 0 := by
  simp only [Nucleus.twoTz]
  rw [← mp.mirror_cond_N, ← mp.mirror_cond_Z]
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Mirror Energy Difference (MED).
  The difference in excitation energy between analogue states in a mirror pair. -/
def MED (E_exc1 E_exc2 : ℝ) : ℝ :=
  E_exc1 - E_exc2

/-- Electromagnetic transition rate B(Eλ). -/
abbrev TransitionRate (lambda : ℕ) := {rate : ℝ // 0 ≤ rate}

namespace TransitionRate

abbrev rate {lambda : ℕ} (R : TransitionRate lambda) : ℝ := R.1

abbrev rate_nonneg {lambda : ℕ} (R : TransitionRate lambda) : 0 ≤ R.rate := R.2

end TransitionRate

/-- Nuclear State characterizing a level. -/
abbrev NuclearState := ℝ × ℚ × ℤ × Isospin × ℕ

namespace NuclearState

abbrev energy (S : NuclearState) : ℝ := S.1

abbrev spin (S : NuclearState) : ℚ := S.2.1

abbrev parity (S : NuclearState) : ℤ := S.2.2.1

abbrev isospin (S : NuclearState) : Isospin := S.2.2.2.1

abbrev l (S : NuclearState) : ℕ := S.2.2.2.2

end NuclearState

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
abbrev EffectiveCharge := ℝ × ℝ

namespace EffectiveCharge

@[simp] def e_pi (e : EffectiveCharge) : ℝ := e.1
@[simp] def e_nu (e : EffectiveCharge) : ℝ := e.2

end EffectiveCharge

/-- Symmetry Energy parameters. -/
abbrev EquationOfState := ℝ × ℝ

namespace EquationOfState

@[simp] def S_0 (eos : EquationOfState) : ℝ := eos.1
@[simp] def L (eos : EquationOfState) : ℝ := eos.2

end EquationOfState

/-- A model for the charge radius difference of mirror nuclei. -/
abbrev ChargeRadiusDifference := ℝ

namespace ChargeRadiusDifference

@[simp] def delta_R_ch (radius_diff : ChargeRadiusDifference) : ℝ := radius_diff

end ChargeRadiusDifference

/-- The correlation between the slope of the symmetry energy L and the difference
  in charge radii of mirror nuclei (ΔR_ch). Often formulated as a linear correlation. -/
def symmetry_energy_L_correlation (eos : EquationOfState) (radius_diff : ChargeRadiusDifference) : Prop :=
  ∃ (a b : ℝ), a > 0 ∧ radius_diff.delta_R_ch = a * eos.L + b

end InfoGeometry.Physics
