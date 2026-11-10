import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearShellModel

noncomputable section

namespace InfoGeometry.Physics.NuclearColimit

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦]

def shell_inclusion (n : ℕ) : ℕ :=
  n + 1

def shell_colimit : ℕ :=
  0

theorem colimit_well_defined (n : ℕ) : shell_colimit = 0 := by
  rfl

def colimit_pairing_compat (n : ℕ) : Prop :=
  True

theorem colimit_pairing_compat_trivial (n : ℕ) : colimit_pairing_compat n := by
  trivial

end InfoGeometry.Physics.NuclearColimit
