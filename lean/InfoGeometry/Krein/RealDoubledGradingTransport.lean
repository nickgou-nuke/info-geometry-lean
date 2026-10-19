/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.RealDoubledHilbertBridge
import InfoGeometry.Krein.Clifford

/-!
# Grading transport on the real doubled carrier

This owner keeps the Krein grading separate from the modular and spectral
generators.  A source grading is transported only under an explicit
intertwining equation; no equality between `gradeCLM`, `modular_j`, and
`spectral_epsilon` is inferred.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [KreinGradedModule (DoubledSpace E)]

local notation "Γ₀" => KreinGradedModule.gradeCLM (H := DoubledSpace E)
local notation "Γ₁" => KreinGradedModule.gradeCLM (H := HilbertDoubled E)

/-!
The source-to-target grading equation is the required soldering datum.  It is
kept as a hypothesis because the repository does not identify the canonical
source grading with either doubled-space Cl(1,1) generator by default.
-/

theorem conjugateDoubledEnd_gradeCLM
    (hΓ :
      (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp Γ₀ =
        Γ₁.comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap) :
    conjugateDoubledEnd (E := E) Γ₀ = Γ₁ := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun f : DoubledSpace E →L[ℝ] HilbertDoubled E =>
    f ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)) x)) hΓ
  simpa [conjugateDoubledEnd, ContinuousLinearMap.comp_apply] using h

theorem conjugateDoubledEnd_gradeConj
    (hΓ :
      (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp Γ₀ =
        Γ₁.comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap)
    (T : DoubledSpace E →L[ℝ] DoubledSpace E) :
    KreinGradedModule.gradeConj (H := HilbertDoubled E)
        (conjugateDoubledEnd (E := E) T) =
      conjugateDoubledEnd (E := E)
        (KreinGradedModule.gradeConj (H := DoubledSpace E) T) := by
  unfold KreinGradedModule.gradeConj
  have hconj : conjugateDoubledEnd (E := E) Γ₀ = Γ₁ :=
    conjugateDoubledEnd_gradeCLM (E := E) hΓ
  rw [← hconj]
  rw [← conjugateDoubledEnd_comp, ← conjugateDoubledEnd_comp]

theorem conjugateDoubledEnd_isEven
    (hΓ :
      (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp Γ₀ =
        Γ₁.comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap)
    (T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hT : KreinGradedModule.IsEven (H := DoubledSpace E) T) :
    KreinGradedModule.IsEven (H := HilbertDoubled E)
      (conjugateDoubledEnd (E := E) T) := by
  unfold KreinGradedModule.IsEven
  rw [conjugateDoubledEnd_gradeConj (E := E) hΓ T]
  exact congrArg (conjugateDoubledEnd (E := E)) hT

theorem conjugateDoubledEnd_isOdd
    (hΓ :
      (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp Γ₀ =
        Γ₁.comp
          (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap)
    (T : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hT : KreinGradedModule.IsOdd (H := DoubledSpace E) T) :
    KreinGradedModule.IsOdd (H := HilbertDoubled E)
      (conjugateDoubledEnd (E := E) T) := by
  unfold KreinGradedModule.IsOdd
  rw [conjugateDoubledEnd_gradeConj (E := E) hΓ T]
  exact congrArg (conjugateDoubledEnd (E := E)) hT

end InfoGeometry.Krein
