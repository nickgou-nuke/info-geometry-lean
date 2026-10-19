/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Krein.Clifford

/-!
# Real doubled Hilbert/Krein transport

This module is the first executable slice of the real-first reconciliation
plan.  It transports the canonical doubled real `Cl(1,1)` action through the
existing `ULift` Hilbert carrier without changing scalars or identifying the
sheet swap with the Krein fundamental symmetry.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The existing `DoubledSpace`/`HilbertDoubled` equivalence as a Krein isometry. -/
noncomputable def doubledToHilbertKreinEquiv :
    KreinEquiv (DoubledSpace E) (HilbertDoubled E) where
  toContinuousLinearEquiv := HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)
  isometric := by
    intro u v
    rfl

/-- Transport of the canonical real split action to the `ULift` carrier. -/
noncomputable def hilbertDoubledCl11Action :
    Quantum.RealSplitCl11Action (HilbertDoubled E) :=
  Quantum.RealSplitCl11Action.ofContinuousLinearEquiv
    (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E))
    (Quantum.doubledSpaceCl11Action (E := E))

/-- Conjugation of a bounded real operator through the existing carrier equivalence. -/
noncomputable def conjugateDoubledEnd (T : DoubledSpace E →L[ℝ] DoubledSpace E) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  (HilbertDoubled.ofDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap.comp
    (T.comp
      (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).toContinuousLinearMap)

theorem conjugateDoubledEnd_comp
    (S T : DoubledSpace E →L[ℝ] DoubledSpace E) :
    conjugateDoubledEnd (E := E) (S.comp T) =
      (conjugateDoubledEnd (E := E) S).comp
        (conjugateDoubledEnd (E := E) T) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [conjugateDoubledEnd]

theorem conjugateDoubledEnd_id :
    conjugateDoubledEnd (E := E) (ContinuousLinearMap.id ℝ (DoubledSpace E)) =
      ContinuousLinearMap.id ℝ (HilbertDoubled E) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [conjugateDoubledEnd]

/-- The transported `ε` generator is exactly conjugation of the doubled-space one. -/
theorem conjugateDoubledEnd_eps :
    conjugateDoubledEnd (E := E)
        (Quantum.doubledSpaceCl11Action (E := E)).eps =
      (hilbertDoubledCl11Action (E := E)).eps := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The transported modular `J` generator is exactly conjugation of the doubled-space one. -/
theorem conjugateDoubledEnd_J :
    conjugateDoubledEnd (E := E)
        (Quantum.doubledSpaceCl11Action (E := E)).J =
      (hilbertDoubledCl11Action (E := E)).J := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The canonical doubled grading transports to the concrete Hilbert swap. -/
theorem conjugateDoubledEnd_modular_j_hilbertSwap :
    conjugateDoubledEnd (E := E) (modular_j (E := E)) =
      hilbertSwapCLM := by
  apply ContinuousLinearMap.ext
  intro x
  apply (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)).injective
  change modular_j (E := E)
      ((HilbertDoubled.toDoubledContinuousLinearEquiv (E := E)) x) =
    (HilbertDoubled.toDoubledContinuousLinearEquiv (E := E))
      (hilbertSwapCLM x)
  exact (toDoubled_hilbertSwapCLM_apply (E := E) x).symm

@[simp] theorem hilbertDoubledCl11Action_K_sq :
    (hilbertDoubledCl11Action (E := E)).K.comp
        (hilbertDoubledCl11Action (E := E)).K =
      -(ContinuousLinearMap.id ℝ (HilbertDoubled E)) := by
  simpa using
    (Quantum.RealSplitCl11Action.K_sq
      (hilbertDoubledCl11Action (E := E)))

/-- The derived square-minus-one axis anticommutes with the transported
    pseudoscalar generator.  This is the operator-level `Cl(1,1)` relation
    needed by later graded and Krein-cycle transport. -/
theorem hilbertDoubledCl11Action_K_eps_anticommute :
    (hilbertDoubledCl11Action (E := E)).K.comp
        (hilbertDoubledCl11Action (E := E)).eps =
      -((hilbertDoubledCl11Action (E := E)).eps.comp
        (hilbertDoubledCl11Action (E := E)).K) := by
  have h := congrArg (fun T : HilbertDoubled E →L[ℝ] HilbertDoubled E =>
    T.comp (hilbertDoubledCl11Action (E := E)).eps)
    (hilbertDoubledCl11Action (E := E)).J_eps_anti
  simpa [Quantum.RealSplitCl11Action.K, ContinuousLinearMap.comp_assoc,
    (hilbertDoubledCl11Action (E := E)).eps_sq] using h

end InfoGeometry.Krein
