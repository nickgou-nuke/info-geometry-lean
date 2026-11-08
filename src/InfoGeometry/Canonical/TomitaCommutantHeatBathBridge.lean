import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.MaurerCartanFactorization
import InfoGeometry.Canonical.KleinBottleTomitaCrosscapBridge
import InfoGeometry.Canonical.ThermodynamicsFirstLaw
import InfoGeometry.KMSGNS

noncomputable section

namespace InfoGeometry.Canonical.TomitaCommutant

open InfoGeometry.Modular.ExactSequence
open InfoGeometry.Canonical.KleinBottleTomitaCrosscap

variable {B : Type*} [Ring B]

def bracket (x y : B) : B :=
  x * y - y * x

@[simp] theorem bracket_apply (x y : B) : bracket x y = x * y - y * x := rfl

def inCommutant (M : Set B) (b : B) : Prop :=
  ∀ m ∈ M, bracket m b = 0

def commutant (M : Set B) : Set B :=
  {b : B | inCommutant M b}

theorem zero_mem_commutant (M : Set B) : (0 : B) ∈ commutant M := by
  intro m _
  simp [bracket]

theorem add_mem_commutant (M : Set B) {b₁ b₂ : B}
    (h₁ : b₁ ∈ commutant M) (h₂ : b₂ ∈ commutant M) :
    b₁ + b₂ ∈ commutant M := by
  intro m hm
  have h1m := h₁ m hm
  have h2m := h₂ m hm
  dsimp [bracket] at *
  have h₃ : m * (b₁ + b₂) - (b₁ + b₂) * m = (m * b₁ - b₁ * m) + (m * b₂ - b₂ * m) := by
    calc
      m * (b₁ + b₂) - (b₁ + b₂) * m = (m * b₁ + m * b₂) - (b₁ * m + b₂ * m) := by
        simp [mul_add, add_mul]
      _ = (m * b₁ - b₁ * m) + (m * b₂ - b₂ * m) := by
        abel
  rw [h₃]
  have h₄ : m * b₁ - b₁ * m = 0 := by simpa [bracket] using h₁ m hm
  have h₅ : m * b₂ - b₂ * m = 0 := by simpa [bracket] using h₂ m hm
  rw [h₄, h₅]
  <;> simp [add_zero]

theorem mul_mem_commutant (M : Set B) {b₁ b₂ : B}
    (h₁ : b₁ ∈ commutant M) (h₂ : b₂ ∈ commutant M) :
    b₁ * b₂ ∈ commutant M := by
  intro m hm
  have h1m := h₁ m hm
  have h2m := h₂ m hm
  dsimp [bracket] at *
  have hm1 : m * b₁ = b₁ * m := by
    have h₁' : m * b₁ - b₁ * m = 0 := by simpa [bracket] using h₁ m hm
    have h₂' : m * b₁ = b₁ * m := by
      apply eq_of_sub_eq_zero
      simpa [sub_eq_add_neg] using h₁'
    exact h₂'
  have hm2 : m * b₂ = b₂ * m := by
    have h₁' : m * b₂ - b₂ * m = 0 := by simpa [bracket] using h₂ m hm
    have h₂' : m * b₂ = b₂ * m := by
      apply eq_of_sub_eq_zero
      simpa [sub_eq_add_neg] using h₁'
    exact h₂'
  calc
    m * (b₁ * b₂) - (b₁ * b₂) * m = (m * b₁) * b₂ - b₁ * (b₂ * m) := by
      simp only [mul_assoc]
    _ = (b₁ * m) * b₂ - b₁ * (m * b₂) := by rw [hm1, hm2]
    _ = b₁ * (m * b₂) - b₁ * (m * b₂) := by simp [mul_assoc]
    _ = 0 := by simp [sub_self]

def centerOf (M : Set B) : Set B :=
  {c ∈ M | ∀ m ∈ M, bracket m c = 0}

theorem center_eq_inter_commutant (M : Set B) :
    centerOf M = M ∩ commutant M := by
  apply Set.Subset.antisymm
  · -- Prove centerOf M ⊆ M ∩ commutant M
    intro c hc
    have h₁ : c ∈ M := hc.1
    have h₂ : ∀ m ∈ M, bracket m c = 0 := hc.2
    have h₃ : c ∈ commutant M := by
      intro m hm
      exact h₂ m hm
    exact ⟨h₁, h₃⟩
  · -- Prove M ∩ commutant M ⊆ centerOf M
    intro c hc
    have h₁ : c ∈ M := hc.1
    have h₂ : c ∈ commutant M := hc.2
    have h₃ : ∀ m ∈ M, bracket m c = 0 := by
      intro m hm
      exact h₂ m hm
    exact ⟨h₁, h₃⟩

structure TomitaCommutantDatum (B : Type*) [Ring B] where
  M : Set B
  J : B → B
  J_involutive : ∀ x : B, J (J x) = x
  J_mul : ∀ x y : B, J (x * y) = J y * J x
  J_maps_to_commutant : ∀ m ∈ M, J m ∈ commutant M

theorem tomita_crosscap_commutation (D : TomitaCommutantDatum B) (m m' : B)
    (hm : m ∈ D.M) (hm' : m' ∈ D.M) :
    bracket m (D.J m') = 0 := by
  have h_comm := D.J_maps_to_commutant m' hm'
  exact h_comm m hm

theorem modular_reflected_hamiltonian_in_commutant (D : TomitaCommutantDatum B) (K : B)
    (hK : K ∈ D.M) :
    ∀ m ∈ D.M, bracket m (D.J K) = 0 := by
  intro m hm
  exact tomita_crosscap_commutation D m K hm hK

theorem quantum_klein_bottle_duality (D : TomitaCommutantDatum B) :
    (0 : B) ∈ commutant D.M ∧
    centerOf D.M = D.M ∩ commutant D.M ∧
    (∀ m m' : B, m ∈ D.M → m' ∈ D.M → bracket m (D.J m') = 0) := by
  refine' ⟨zero_mem_commutant D.M, center_eq_inter_commutant D.M, ?_⟩
  intro m m' hm hm'
  exact tomita_crosscap_commutation D m m' hm hm'

end InfoGeometry.Canonical.TomitaCommutant

end noncomputable section