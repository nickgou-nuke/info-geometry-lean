import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearRotationalBand

noncomputable section

namespace InfoGeometry.Physics.NuclearGiantResonance

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦]

variable (e₂ : 𝒦)
variable (r₀ : 𝒦)
variable (nucleon_mass : 𝒦)
variable (charge_z : 𝒦)
variable (fine_structure : 𝒦)

def gdr_energy (mass_number : ℕ) : 𝒦 :=
  (518 : 𝒦) / (10 : 𝒦) / (mass_number : 𝒦)

def e1_selection_rule (l_initial : ℕ) (l_final : ℕ) : Prop :=
  l_final = l_initial + 1 ∨ l_final = l_initial - 1 ∨ l_final = l_initial

theorem e1_selection_abs (l : ℕ) : e1_selection_rule l (l + 1) := by
  exact Or.inl (by rfl)

theorem e1_selection_emission (l : ℕ) (h : l > 0) : e1_selection_rule l (l - 1) := by
  cases l with
  | zero => exfalso; omega
  | succ l' =>
    simp_all [Nat.succ_pred]
    <;>
    (try omega) <;>
    (try tauto) <;>
    (try
      {
        exact Or.inr (Or.inl (by rfl))
      })

def e1_parity_change (pi_initial : 𝒦) (pi_final : 𝒦) : Prop :=
  pi_final = - pi_initial

theorem e1_parity_change_holds (pi : 𝒦) : e1_parity_change pi (- pi) := by
  rfl

def m1_selection_rule (l_initial : ℕ) (l_final : ℕ) : Prop :=
  l_final = l_initial + 1 ∨ l_final = l_initial - 1 ∨ l_final = l_initial

def m1_parity_preserve (pi_initial : 𝒦) (pi_final : 𝒦) : Prop :=
  pi_final = pi_initial

theorem m1_parity_preserve_holds (pi : 𝒦) : m1_parity_preserve pi pi := by
  rfl

end InfoGeometry.Physics.NuclearGiantResonance
