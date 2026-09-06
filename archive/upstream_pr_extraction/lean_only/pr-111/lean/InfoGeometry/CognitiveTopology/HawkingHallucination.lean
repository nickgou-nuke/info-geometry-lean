import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.CognitiveTopology.ExceptionalPointGrokking

/-!
# Thermal noise beside an exceptional-point property

This module keeps the "hallucination as Hawking radiation" slogan out of the
theorem surface.  It proves only that, from explicit premises, the nilpotent
exceptional-point datum and a positive temperature/noise parameter can be
carried together.

#### BUCKET 1: CLOSED FINITE THEOREMS

None.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`exceptionalPoint_with_positive_temperature`.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here identifies LLM hallucination with Hawking radiation, proves a
sampling distribution, or derives any stochastic inference bound.
-/

noncomputable section

namespace InfoGeometry.CognitiveTopology.Thermodynamics

open ContinuousLinearMap
open InfoGeometry.CognitiveTopology.Grokking

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- The thermodynamic noise parameter carried as an explicit premise.
variable (T : ℝ)

def nilpotentFlow (N : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H + (t : ℂ) • N

theorem nilpotentFlow_apply (N : H →L[ℂ] H) (t : ℝ) (x : H) :
    nilpotentFlow N t x = x + (t : ℂ) • N x := by
  simp [nilpotentFlow]

theorem nilpotentFlow_zero (N : H →L[ℂ] H) :
    nilpotentFlow N 0 = ContinuousLinearMap.id ℂ H := by
  simp [nilpotentFlow]

theorem nilpotentFlow_add (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (s t : ℝ) :
    nilpotentFlow N s ∘L nilpotentFlow N t =
      nilpotentFlow N (s + t) := by
  ext x
  simp only [nilpotentFlow, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [N.map_add, N.map_smul]
  have hNN : N (N x) = 0 := by
    have hx := congrArg (fun f : H →L[ℂ] H => f x) hN
    simpa [ContinuousLinearMap.comp_apply] using hx
  rw [hNN]
  push_cast
  module

theorem nilpotentFlow_inverse (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (t : ℝ) :
    nilpotentFlow N t ∘L nilpotentFlow N (-t) =
      ContinuousLinearMap.id ℂ H := by
  rw [nilpotentFlow_add N hN]
  simp [nilpotentFlow]

theorem nilpotentFlow_left_inverse (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (t : ℝ) :
    nilpotentFlow N (-t) ∘L nilpotentFlow N t =
      ContinuousLinearMap.id ℂ H := by
  rw [nilpotentFlow_add N hN]
  simp [nilpotentFlow]

theorem nilpotentFlow_injective (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (t : ℝ) :
    Function.Injective (nilpotentFlow N t) := by
  intro x y hxy
  have h := congrArg (fun z => nilpotentFlow N (-t) z) hxy
  have hleft := nilpotentFlow_left_inverse N hN t
  have hx := congrArg (fun f : H →L[ℂ] H => f x) hleft
  have hy := congrArg (fun f : H →L[ℂ] H => f y) hleft
  have hx' : nilpotentFlow N (-t) (nilpotentFlow N t x) = x := by
    simpa [ContinuousLinearMap.comp_apply] using hx
  have hy' : nilpotentFlow N (-t) (nilpotentFlow N t y) = y := by
    simpa [ContinuousLinearMap.comp_apply] using hy
  calc
    x = nilpotentFlow N (-t) (nilpotentFlow N t x) := hx'.symm
    _ = nilpotentFlow N (-t) (nilpotentFlow N t y) := h
    _ = y := hy'

theorem nilpotentFlow_surjective (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (t : ℝ) :
    Function.Surjective (nilpotentFlow N t) := by
  intro y
  refine ⟨nilpotentFlow N (-t) y, ?_⟩
  have h := nilpotentFlow_inverse N hN t
  have hy := congrArg (fun f : H →L[ℂ] H => f y) h
  simpa [ContinuousLinearMap.comp_apply] using hy

theorem nilpotentFlow_bijective (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (t : ℝ) :
    Function.Bijective (nilpotentFlow N t) :=
  ⟨nilpotentFlow_injective N hN t, nilpotentFlow_surjective N hN t⟩

theorem nilpotentFlow_commute (N : H →L[ℂ] H)
    (hN : N ∘L N = 0) (s t : ℝ) :
    nilpotentFlow N s ∘L nilpotentFlow N t =
      nilpotentFlow N t ∘L nilpotentFlow N s := by
  rw [nilpotentFlow_add N hN, nilpotentFlow_add N hN, add_comm]

theorem exceptionalPoint_displacement_flow_bijective
    (A N : H →L[ℂ] H) (h_ep : IsExceptionalPoint A N) (t : ℝ) :
    Function.Bijective (nilpotentFlow (A - ContinuousLinearMap.id ℂ H) t) := by
  rw [exceptionalPoint_displacement_eq_nilpotent_part A N h_ep]
  exact nilpotentFlow_bijective N h_ep.2 t

/--
Conditional thermal datum.

From an explicit exceptional-point property and a positive temperature/noise
premise, we can carry both the square-zero nilpotent part and the positivity
fact.  This does not identify the noise with hallucination or Hawking radiation.
-/
theorem exceptionalPoint_with_positive_temperature (A N : H →L[ℂ] H)
    (h_ep : IsExceptionalPoint A N) (h_T_pos : T > 0) :
    (N ∘L N = 0) ∧ T > 0 := by
  refine ⟨?_, ?_⟩
  · exact exceptionalPoint_nilpotent_part_square_zero A N h_ep
  · exact h_T_pos

theorem exceptionalPoint_with_positive_temperature_displacement
    (A N : H →L[ℂ] H)
    (h_ep : IsExceptionalPoint A N) (h_T_pos : T > 0) :
    (N ∘L N = 0) ∧
      ((A - ContinuousLinearMap.id ℂ H) ∘L
        (A - ContinuousLinearMap.id ℂ H) = 0) ∧ T > 0 := by
  refine ⟨exceptionalPoint_nilpotent_part_square_zero A N h_ep, ?_, h_T_pos⟩
  exact exceptionalPoint_displacement_square_zero A N h_ep

end InfoGeometry.CognitiveTopology.Thermodynamics
