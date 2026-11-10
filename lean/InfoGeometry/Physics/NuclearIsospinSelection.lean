import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry

noncomputable section

namespace InfoGeometry.Physics.NuclearIsospinSelection

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

def strong_isospin_selection (t_initial : ℕ) (t_final : ℕ) : Prop :=
  t_final = t_initial

theorem strong_isospin_conserved (t : ℕ) : strong_isospin_selection t t := by
  rfl

def em_isospin_selection (t_initial : ℕ) (t_final : ℕ) : Prop :=
  t_final = t_initial ∨ t_final = t_initial + 1 ∨ t_initial = t_final + 1

theorem em_isospin_delta_zero (t : ℕ) : em_isospin_selection t t := by
  exact Or.inl (by rfl)

theorem em_isospin_delta_one (t : ℕ) : em_isospin_selection t (t + 1) := by
  exact Or.inr (Or.inl (by rfl))

theorem em_isospin_delta_minus_one (t : ℕ) : em_isospin_selection (t + 1) t := by
  exact Or.inr (Or.inr (by rfl))

def em_parity_selection (l : ℕ) (pi_initial : 𝒦) (pi_final : 𝒦) : Prop :=
  pi_final = (-1 : 𝒦) ^ l * pi_initial

theorem e1_parity_selection (pi : 𝒦) : em_parity_selection 1 pi (- pi) := by
  norm_num [em_parity_selection]
  <;> rfl

def m1_parity_selection (l : ℕ) (pi_initial : 𝒦) (pi_final : 𝒦) : Prop :=
  pi_final = pi_initial

theorem m1_parity_selection_holds (pi : 𝒦) : m1_parity_selection 1 pi pi := by
  rfl

theorem e2_parity_selection (pi : 𝒦) : em_parity_selection 2 pi pi := by
  norm_num [em_parity_selection]
  <;> rfl

end InfoGeometry.Physics.NuclearIsospinSelection
