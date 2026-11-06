/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Bounded intertwiners determined by a cyclic vector

For a family of bounded source operators, cyclicity means density of the
linear span of the orbit of a specified vector. An intertwiner is then
determined by its value on that vector. The two operator families need not
commute, and their source and target spaces may be different.

These are uniqueness statements for actual continuous linear maps. They do
not construct an intertwiner for every target vector or construct a relative
tensor product, a conformal net, or a categorical braiding.
-/

namespace InfoGeometry.OperatorAlgebra.CyclicIntertwiner

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : ι → E →L[𝕜] E} {B : ι → F →L[𝕜] F} {Ω : E}

/-- Two bounded intertwiners agreeing at a cyclic vector are equal.

The intertwining order is `T ∘ A i = B i ∘ T`; neither order of operators
within the source or target family is exchanged. -/
theorem eq_of_eval_eq
    (hΩ : Dense (Submodule.span 𝕜 (Set.range fun i => A i Ω) : Set E))
    {T S : E →L[𝕜] F}
    (hT : ∀ i, T.comp (A i) = (B i).comp T)
    (hS : ∀ i, S.comp (A i) = (B i).comp S)
    (hEval : T Ω = S Ω) : T = S := by
  apply ContinuousLinearMap.ext_on hΩ
  rintro _ ⟨i, rfl⟩
  calc
    T (A i Ω) = B i (T Ω) := congrArg (fun R : E →L[𝕜] F => R Ω) (hT i)
    _ = B i (S Ω) := congrArg (B i) hEval
    _ = S (A i Ω) := (congrArg (fun R : E →L[𝕜] F => R Ω) (hS i)).symm

/-- An intertwiner is zero exactly when it annihilates the cyclic vector. -/
theorem eq_zero_iff_eval_eq_zero
    (hΩ : Dense (Submodule.span 𝕜 (Set.range fun i => A i Ω) : Set E))
    {T : E →L[𝕜] F}
    (hT : ∀ i, T.comp (A i) = (B i).comp T) : T = 0 ↔ T Ω = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hEval
    exact eq_of_eval_eq hΩ hT (by intro i; simp) hEval

end InfoGeometry.OperatorAlgebra.CyclicIntertwiner
