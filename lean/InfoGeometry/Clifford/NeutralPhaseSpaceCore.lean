import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.NeutralPhaseSpaceCore

Generic neutral phase-space owner on `E × E*`.

This file is deliberately algebraic:

- the carrier is `E × Module.Dual ℝ E`,
- the canonical neutral bilinear form is built from evaluation pairing,
- the associated quadratic form is the off-diagonal neutral form,
- the Clifford algebra is defined over that quadratic form.

No doubled/Krein realization is imported here.
-/

namespace InfoGeometry.Clifford.NeutralPhaseSpaceCore

universe u

/-- Generic neutral phase-space carrier `E × E*`. -/
@[rep_depth krein]
abbrev PhaseSpaceCarrier (E : Type u) [AddCommGroup E] [Module ℝ E] : Type u :=
  E × Module.Dual ℝ E

section Core

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Symmetric evaluation bilinear form on `E × E*`. -/
@[rep_depth krein]
noncomputable def canonicalNeutralBilin : LinearMap.BilinForm ℝ (PhaseSpaceCarrier E) :=
  LinearMap.compl₁₂ (LinearMap.dualProd ℝ E)
    (LinearEquiv.prodComm ℝ E (Module.Dual ℝ E)).toLinearMap
    (LinearEquiv.prodComm ℝ E (Module.Dual ℝ E)).toLinearMap

/-- Canonical neutral quadratic form on `E × E*`. -/
@[rep_depth krein]
noncomputable def canonicalNeutralForm : QuadraticForm ℝ (PhaseSpaceCarrier E) :=
  (canonicalNeutralBilin (E := E)).toQuadraticMap

@[rep_depth krein, simp] theorem canonicalNeutralBilin_apply
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) X Y = X.2 Y.1 + Y.2 X.1 := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [canonicalNeutralBilin, add_comm]

@[rep_depth krein, simp] theorem canonicalNeutralForm_apply
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralForm (E := E) X = 2 * X.2 X.1 := by
  rcases X with ⟨x, ξ⟩
  simp [canonicalNeutralForm, canonicalNeutralBilin]
  ring

@[rep_depth krein, simp] theorem canonicalNeutralForm_fst_zero
    (ξ : Module.Dual ℝ E) :
    canonicalNeutralForm (E := E) (0, ξ) = 0 := by
  simp [canonicalNeutralForm_apply]

@[rep_depth krein, simp] theorem canonicalNeutralForm_snd_zero
    (x : E) :
    canonicalNeutralForm (E := E) (x, 0) = 0 := by
  simp [canonicalNeutralForm_apply]

/-- Clifford algebra over the canonical neutral phase-space form. -/
@[rep_depth operator]
abbrev NeutralPhaseClifford (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  CliffordAlgebra (canonicalNeutralForm (E := E))

end Core

end InfoGeometry.Clifford.NeutralPhaseSpaceCore
