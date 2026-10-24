/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceWeylSynthesis
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Exact integral noncommutative models and counterexamples to overstatements
in the intake. The finite model is not a substitute for an exceptional algebra
or a von Neumann algebra. Ordinary `decide` is kernel-checked here. -/

namespace InfoGeometry.Canonical.PeirceWeylExamples

open Matrix
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Core.PeirceWeylUnits
open InfoGeometry.Core.JordanMultiplicationClosure

/-- Integral upper matrix unit. -/
def d₂ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Integral lower matrix unit. -/
def b₂ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

theorem integral_pair : IsMoorePenroseInverse d₂ b₂ ∧ d₂ * d₂ = 0 := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  · decide

theorem integral_noncommutative : d₂ * b₂ ≠ b₂ * d₂ := by decide

theorem integral_weyl_and_third :
    weylElement d₂ b₂ = !![0, 1; -1, 0] ∧
    thirdRoot d₂ b₂ = !![0, 1; -1, -1] ∧
    -majoranaMinus d₂ b₂ * thirdRoot d₂ b₂ = !![1, 1; 0, 1] := by decide

/-- The involution polynomial `t²-1` is not `Φ₂(t)=t+1`. -/
theorem grading_not_cyclotomic_two : chiralSupport d₂ b₂ + activeSupport d₂ b₂ ≠ 0 := by
  decide

/-- The source's nested-commutator order gives the opposite, nonzero answer. -/
theorem source_jordan_sign_counterexample :
    (d₂ * (b₂ * d₂ + d₂ * b₂) + (b₂ * d₂ + d₂ * b₂) * d₂) -
      (b₂ * (d₂ * d₂ + d₂ * d₂) + (d₂ * d₂ + d₂ * d₂) * b₂) ≠
        (b₂ * d₂ - d₂ * b₂) * d₂ - d₂ * (b₂ * d₂ - d₂ * b₂) := by decide

/-- Even this square-zero MP pair has a nonzero Jordan associator. -/
theorem square_zero_associator_nonzero :
    ((d₂ * d₂ + d₂ * d₂) * b₂ + b₂ * (d₂ * d₂ + d₂ * d₂)) -
      (d₂ * (d₂ * b₂ + b₂ * d₂) + (d₂ * b₂ + b₂ * d₂) * d₂) ≠ 0 := by decide

/-- An actual proper active corner with one harmonic coordinate. -/
def d₃ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

def b₃ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

theorem proper_corner_pair : IsMoorePenroseInverse d₃ b₃ ∧ d₃ * d₃ = 0 := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  · decide

theorem proper_corner_distinctions :
    activeSupport d₃ b₃ ≠ 1 ∧
    thirdRoot d₃ b₃ ^ 3 = activeSupport d₃ b₃ ∧
    thirdRoot d₃ b₃ ^ 3 ≠ 1 ∧
    weylElement d₃ b₃ ^ 4 = 1 ∧
    weylElement d₃ b₃ = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by decide

#check @InfoGeometry.Canonical.PeirceWeylSynthesis.peirce_weyl_trace_synthesis
#check @weylUnit
#check @weyl_conjugation
#check @InfoGeometry.Core.PeirceDensityIntertwining.density_trace_boundary
#check @commutator_apply
#check @commutator_leibniz

end InfoGeometry.Canonical.PeirceWeylExamples
