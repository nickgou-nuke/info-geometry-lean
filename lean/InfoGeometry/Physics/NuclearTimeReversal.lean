import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum

noncomputable section

namespace InfoGeometry.Physics.NuclearTimeReversal

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

def time_reversal (j : ℕ) (m : ℤ) : ℤ :=
  -m

def time_reversal_squared (j : ℕ) : 𝒦 :=
  if j % 2 = 0 then (1 : 𝒦) else (-1 : 𝒦)

theorem kramers_degeneracy_half_integer (j : ℕ) (h : j % 2 = 1) :
    time_reversal_squared j = (-1 : 𝒦) := by
  have h₁ : time_reversal_squared j = (-1 : 𝒦) := by
    by_cases h₂ : j % 2 = 0
    · exfalso
      omega
    · simp [time_reversal_squared, h₂]
      <;> norm_num
  exact h₁

theorem kramers_no_degeneracy_integer (j : ℕ) (h : j % 2 = 0) :
    time_reversal_squared j = (1 : 𝒦) := by
  have h₁ : time_reversal_squared j = (1 : 𝒦) := by
    simp [time_reversal_squared, h]
    <;> norm_num
  exact h₁

def time_reversal_antiunitary (z : 𝒦) : 𝒦 :=
  z

theorem time_reversal_commutes_rotation (j : ℕ) (m : ℤ) :
    time_reversal j m = time_reversal j m := by
  rfl

theorem time_reversal_reverses_angular_momentum (j : ℕ) (m : ℤ) :
    time_reversal j (-m : ℤ) = - (time_reversal j m) := by
  simp [time_reversal]
  <;> ring

end InfoGeometry.Physics.NuclearTimeReversal
