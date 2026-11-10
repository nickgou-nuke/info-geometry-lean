import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum
import InfoGeometry.Physics.NuclearShellModel
import InfoGeometry.Physics.NuclearPairing
import InfoGeometry.Physics.NuclearRotationalBand
import InfoGeometry.Physics.NuclearGiantResonance
import InfoGeometry.Physics.NuclearTimeReversal
import InfoGeometry.Physics.NuclearIsospinSelection

noncomputable section

namespace InfoGeometry.Physics.NuclearCanonicalBridge

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦]

def nuclear_to_tetractys (two_j : ℕ) (occ : ℕ) (two_t3 : ℕ) (parity : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (two_j, occ, two_t3, parity)

def parity_preserved (parity : ℕ) : Prop :=
  parity = 0 ∨ parity = 1

theorem parity_binary (p : ℕ) (h : p = 0 ∨ p = 1) : parity_preserved p := by
  exact h

def car_to_clifford (i : ℕ) : ℕ × ℕ :=
  (2 * i - 1, 2 * i)

def clifford_anticommutator (i : ℕ) (j : ℕ) : ℕ :=
  if i = j then 2 else 0

theorem clifford_anticommutator_diagonal (i : ℕ) : clifford_anticommutator i i = 2 := by
  have h₁ : clifford_anticommutator i i = 2 := by
    simp [clifford_anticommutator]
    <;> norm_num
  exact h₁

theorem clifford_anticommutator_offdiagonal (i j : ℕ) (h : i ≠ j) : clifford_anticommutator i j = 0 := by
  have h₁ : clifford_anticommutator i j = 0 := by
    by_cases h₂ : i = j
    · exfalso
      apply h
      exact h₂
    · simp [clifford_anticommutator, h₂]
      <;> norm_num
  exact h₁

end InfoGeometry.Physics.NuclearCanonicalBridge
