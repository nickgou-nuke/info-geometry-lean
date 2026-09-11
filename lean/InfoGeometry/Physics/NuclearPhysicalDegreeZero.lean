import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.IsospinSymmetryBreaking
import InfoGeometry.External.Auto.WeakIsospinSU2
import InfoGeometry.Physics.ChiralCausalCone

/-!
# Physical degree-zero nuclear symmetry

This owner promotes the verified Pauli/isospin relations into the canonical
`IsospinAlgebra` record.  Spin and isospin are kept as two separate copies;
the abstract five-grading is not identified with either copy here.
-/

namespace InfoGeometry.Physics.NuclearPhysicalDegreeZero

noncomputable section

open InfoGeometry.Physics.ChiralCausalCone
open IsospinSymmetryBreaking

def pauliIsospin : IsospinAlgebra where
  T_plus := σPlus
  T_minus := σMinus
  T_z := (1 / 2 : ℂ) • σ3c
  comm_plus_minus := by
    dsimp [σPlus, σMinus, σ3c]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  comm_z_plus := by
    dsimp [σPlus, σ3c]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  comm_z_minus := by
    dsimp [σMinus, σ3c]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

def pauliSpin : IsospinAlgebra := pauliIsospin

def pauliIsospinCopy : IsospinAlgebra := pauliIsospin

theorem pauliSpin_eq_pauliIsospinCopy :
    pauliSpin = pauliIsospinCopy := rfl

theorem pauliSpin_comm_plus_minus :
    pauliSpin.T_plus * pauliSpin.T_minus -
        pauliSpin.T_minus * pauliSpin.T_plus =
      2 • pauliSpin.T_z :=
  pauliSpin.comm_plus_minus

theorem pauliIsospinCopy_comm_z_plus :
    pauliIsospinCopy.T_z * pauliIsospinCopy.T_plus -
        pauliIsospinCopy.T_plus * pauliIsospinCopy.T_z =
      pauliIsospinCopy.T_plus :=
  pauliIsospinCopy.comm_z_plus

end

end InfoGeometry.Physics.NuclearPhysicalDegreeZero
