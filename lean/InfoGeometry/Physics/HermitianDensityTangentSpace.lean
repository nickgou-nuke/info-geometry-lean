import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Finite Hermitian density states and their trace-zero tangent carrier. -/

noncomputable section

namespace InfoGeometry.Physics

set_option autoImplicit false

abbrev HermitianDensityState (n : Type*) [Fintype n] :=
  {ρ : Matrix n n ℂ // ρ.IsHermitian ∧ Matrix.trace ρ = 1}

def HermitianDensityTangentSubmodule (n : Type*) [Fintype n] :
    Submodule ℝ (Matrix n n ℂ) where
  carrier := {X : Matrix n n ℂ | X.IsHermitian ∧ Matrix.trace X = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro A B hA hB
    rcases hA with ⟨hAherm, hAtrace⟩
    rcases hB with ⟨hBherm, hBtrace⟩
    exact ⟨Matrix.IsHermitian.add hAherm hBherm,
      by simp [Matrix.trace_add, hAtrace, hBtrace]⟩
  smul_mem' := by
    intro r A hA
    rcases hA with ⟨hAherm, hAtrace⟩
    constructor
    · change A.conjTranspose = A at hAherm
      change (r • A).conjTranspose = r • A
      rw [Matrix.conjTranspose_smul, hAherm]
      simp
    · simp [Matrix.trace_smul, hAtrace]

def HermitianDensityTangent {n : Type*} [Fintype n] (_ρ : HermitianDensityState n) :=
  ↥(HermitianDensityTangentSubmodule n)

theorem tangent_hermitian
    {n : Type*} [Fintype n]
    (ρ : HermitianDensityState n)
    (X : HermitianDensityTangent ρ) :
    X.1.IsHermitian := X.2.1

theorem tangent_trace_zero
    {n : Type*} [Fintype n]
    (ρ : HermitianDensityState n)
    (X : HermitianDensityTangent ρ) :
    Matrix.trace X.1 = 0 := X.2.2

theorem trace_eq_one {n : Type*} [Fintype n] (ρ : HermitianDensityState n) :
    Matrix.trace ρ.1 = 1 := ρ.2.2

end InfoGeometry.Physics
