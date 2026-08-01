import Mathlib.Tactic
import InfoGeometry.Physics.ItakuraSaitoFradkinTseytlin

namespace InfoGeometry.Physics.BostConnesMirrorSymmetry

/-!
# Finite mirror-balance data packet

This file only records explicit data fields and reads them back.  It does not
prove Bost--Connes thermodynamics, a CMB spectrum theorem, a zeta partition
function theorem, or 3D mirror symmetry.
-/

/- Data carrying a supplied one-parameter real function. -/
def PrimonGasProperty := ∀ (β : ℝ), β > 1 → ℝ

namespace PrimonGasProperty

def primon_partition_function (P : PrimonGasProperty) : ∀ (β : ℝ), β > 1 → ℝ := P

end PrimonGasProperty

/-- Distinguished parameter value used by this packet. -/
def critical_temperature_pole : ℝ := 1

/- Finite data for two dimensions equipped with equality witnesses. -/
def MirrorBalanceC2 :=
  {p : ℕ × ℕ // p.1 = p.2 ∧ p.1 - p.2 = 0}

namespace MirrorBalanceC2

def higgs_branch_dim (m : MirrorBalanceC2) : ℕ := m.1.1
def coulomb_branch_dim (m : MirrorBalanceC2) : ℕ := m.1.2

theorem mirror_balance (m : MirrorBalanceC2) :
    m.higgs_branch_dim = m.coulomb_branch_dim :=
  m.2.1

theorem difference_zero (m : MirrorBalanceC2) :
    m.higgs_branch_dim - m.coulomb_branch_dim = 0 :=
  m.2.2

end MirrorBalanceC2

theorem mirrorBalanceC2_difference_zero (m : MirrorBalanceC2) :
  m.higgs_branch_dim - m.coulomb_branch_dim = 0 :=
  m.difference_zero

end InfoGeometry.Physics.BostConnesMirrorSymmetry
