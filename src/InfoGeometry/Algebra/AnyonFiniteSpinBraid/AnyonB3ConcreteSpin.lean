import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AnyonFiniteSpinBraid.AnyonArtinBraidOperators

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-! ## Concrete three-site spin Artin representation -/

/-- Swap the first two sites of a three-site spin configuration. -/
def b3SpinSwap0 : SpinOperator 3 :=
  fun s k =>
    match k with
    | ⟨0, _⟩ => s ⟨1, by decide⟩
    | ⟨1, _⟩ => s ⟨0, by decide⟩
    | ⟨2, _⟩ => s ⟨2, by decide⟩

/-- Swap the last two sites of a three-site spin configuration. -/
def b3SpinSwap1 : SpinOperator 3 :=
  fun s k =>
    match k with
    | ⟨0, _⟩ => s ⟨0, by decide⟩
    | ⟨1, _⟩ => s ⟨2, by decide⟩
    | ⟨2, _⟩ => s ⟨1, by decide⟩

/-- The concrete three-site spin action of the two adjacent `B₃` generators. -/
def b3SpinSigma : ArtinGenerator 3 → SpinOperator 3
  | ⟨0, _⟩ => b3SpinSwap0
  | ⟨1, _⟩ => b3SpinSwap1

/-- The first concrete spin braid generator is the first adjacent swap. -/
theorem b3SpinSigma_zero : b3SpinSigma ⟨0, by decide⟩ = b3SpinSwap0 := by
  rfl

/-- The second concrete spin braid generator is the second adjacent swap. -/
theorem b3SpinSigma_one : b3SpinSigma ⟨1, by decide⟩ = b3SpinSwap1 := by
  rfl

/-- The concrete three-site adjacent swaps satisfy the `B₃` braid relation. -/
theorem b3SpinSwap_braid_relation :
    b3SpinSwap0 ∘ b3SpinSwap1 ∘ b3SpinSwap0 =
      b3SpinSwap1 ∘ b3SpinSwap0 ∘ b3SpinSwap1 := by
  funext s k
  fin_cases k <;> rfl

/-- The concrete three-site generator family satisfies the adjacent Artin law. -/
theorem b3SpinSigma_adjacent :
    ∀ i j : ArtinGenerator 3,
      (i : ℕ) + 1 = j →
        b3SpinSigma i ∘ b3SpinSigma j ∘ b3SpinSigma i =
          b3SpinSigma j ∘ b3SpinSigma i ∘ b3SpinSigma j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  exact b3SpinSwap_braid_relation

/-- The far-commutativity law is vacuous for `B₃`, which has only two adjacent generators. -/
theorem b3SpinSigma_far :
    ∀ i j : ArtinGenerator 3,
      (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i →
        b3SpinSigma i ∘ b3SpinSigma j = b3SpinSigma j ∘ b3SpinSigma i := by
  intro i j hfar
  fin_cases i <;> fin_cases j <;> simp at hfar

/-- Concrete three-site spin Artin braid operators. -/
def b3SpinArtinBraidOperators : ArtinBraidOperators 3 where
  sigma := b3SpinSigma
  braid_adjacent := b3SpinSigma_adjacent
  braid_far_comm := b3SpinSigma_far

/-- The concrete three-site spin operators satisfy the Artin readout laws. -/
theorem b3SpinArtinBraidOperators_packet :
    b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ = b3SpinSwap0 ∧
    b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ = b3SpinSwap1 ∧
    b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ =
      b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ := by
  exact ⟨rfl, rfl, b3SpinSwap_braid_relation⟩

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
