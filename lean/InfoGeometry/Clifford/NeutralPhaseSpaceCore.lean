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
- the associated quadratic form is the off-diagonal neutral form in the
  repository's doubled normalization,
- an unscaled companion quadratic form records the exact evaluation surface
  `q (x, ξ) = ξ x`,
- the Clifford algebra is defined over that quadratic form.

No doubled/Krein realization is imported here.
-/

namespace InfoGeometry.Clifford.NeutralPhaseSpaceCore

universe u

/-- Generic neutral phase-space carrier `E × E*`. -/
@[rep_depth operator]
abbrev PhaseSpaceCarrier (E : Type u) [AddCommGroup E] [Module ℝ E] : Type u :=
  E × Module.Dual ℝ E

section Core

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Symmetric evaluation bilinear form on `E × E*`. -/
@[rep_depth operator]
noncomputable def canonicalNeutralBilin : LinearMap.BilinForm ℝ (PhaseSpaceCarrier E) :=
  LinearMap.compl₁₂ (LinearMap.dualProd ℝ E)
    (LinearEquiv.prodComm ℝ E (Module.Dual ℝ E)).toLinearMap
    (LinearEquiv.prodComm ℝ E (Module.Dual ℝ E)).toLinearMap

/-- Canonical neutral quadratic form on `E × E*`. -/
@[rep_depth operator]
noncomputable def canonicalNeutralForm : QuadraticForm ℝ (PhaseSpaceCarrier E) :=
  (canonicalNeutralBilin (E := E)).toQuadraticMap

/-- Unscaled neutral quadratic form on `E × E*`, normalized so that
`q (x, ξ) = ξ x`. -/
@[rep_depth krein]
noncomputable def canonicalNeutralFormUnscaled : QuadraticForm ℝ (PhaseSpaceCarrier E) :=
  (1 / 2 : ℝ) • canonicalNeutralForm (E := E)

@[rep_depth krein, simp] theorem canonicalNeutralBilin_apply
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E) X Y = X.2 Y.1 + Y.2 X.1 := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [canonicalNeutralBilin, add_comm]

/-! The canonical para-complex involution and skew form on `E ⊕ E*`. -/

@[rep_depth operator]
noncomputable def neutralParaInvolution :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := fun X => (X.1, -X.2)
  map_add' := by
    intro X Y
    refine Prod.ext ?_ ?_
    · rfl
    · simp [add_comm]
  map_smul' := by
    intro r X
    refine Prod.ext ?_ ?_
    · rfl
    · simp

@[rep_depth operator, simp] theorem neutralParaInvolution_apply
    (X : PhaseSpaceCarrier E) :
    neutralParaInvolution X = (X.1, -X.2) := rfl

@[rep_depth operator] theorem neutralParaInvolution_sq :
    neutralParaInvolution (E := E) * neutralParaInvolution = 1 := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, ξ⟩
  refine Prod.ext ?_ ?_
  · rfl
  · simp

@[rep_depth operator] theorem canonicalNeutralBilin_para_anti_isometry
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (E := E)
        (neutralParaInvolution X) (neutralParaInvolution Y) =
      -canonicalNeutralBilin (E := E) X Y := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [canonicalNeutralBilin_apply]
  abel

@[rep_depth operator]
noncomputable def neutralOmega :
    LinearMap.BilinForm ℝ (PhaseSpaceCarrier E) :=
  -((canonicalNeutralBilin (E := E)).compl₂
    (neutralParaInvolution (E := E)))

@[rep_depth operator, simp] theorem neutralOmega_apply
    (X Y : PhaseSpaceCarrier E) :
    neutralOmega (E := E) X Y = Y.2 X.1 - X.2 Y.1 := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [neutralOmega, neutralParaInvolution,
    canonicalNeutralBilin_apply]
  ring

@[rep_depth operator] theorem neutralOmega_skew
    (X Y : PhaseSpaceCarrier E) :
    neutralOmega (E := E) X Y = -neutralOmega (E := E) Y X := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [neutralOmega_apply]

/-! The canonical neutral pairing separates both tensor factors. -/
section Nondegenerate

variable [Module.Projective ℝ E]

theorem canonicalNeutralBilin_nondegenerate :
    (canonicalNeutralBilin (E := E)).Nondegenerate := by
  refine ⟨?_, ?_⟩
  · intro X hX
    rcases X with ⟨x, ξ⟩
    have hx : x = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ x).mp
      intro η
      simpa [canonicalNeutralBilin_apply] using hX (0, η)
    have hξ : ξ = 0 := by
      apply LinearMap.ext
      intro y
      have hy := hX (y, 0)
      simpa [canonicalNeutralBilin_apply, hx] using hy
    simp [hx, hξ]
  · intro Y hY
    rcases Y with ⟨y, η⟩
    have hy : y = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ y).mp
      intro ξ
      simpa [canonicalNeutralBilin_apply] using hY (0, ξ)
    have hη : η = 0 := by
      apply LinearMap.ext
      intro x
      have hx := hY (x, 0)
      simpa [canonicalNeutralBilin_apply, hy] using hx
    simp [hy, hη]

end Nondegenerate

@[rep_depth krein, simp] theorem canonicalNeutralForm_apply
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralForm (E := E) X = 2 * X.2 X.1 := by
  rcases X with ⟨x, ξ⟩
  simp [canonicalNeutralForm, canonicalNeutralBilin]
  ring

@[rep_depth krein, simp] theorem canonicalNeutralFormUnscaled_apply
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralFormUnscaled (E := E) X = X.2 X.1 := by
  rcases X with ⟨x, ξ⟩
  simp [canonicalNeutralFormUnscaled, canonicalNeutralForm_apply]

/-- Polarization of evaluation recovers the symmetric neutral pairing. -/
@[rep_depth krein, simp] theorem canonicalNeutralFormUnscaled_polar
    (X Y : PhaseSpaceCarrier E) :
    QuadraticMap.polar (canonicalNeutralFormUnscaled (E := E)) X Y =
      canonicalNeutralBilin X Y := by
  simp [QuadraticMap.polar, canonicalNeutralBilin_apply, map_add]
  ring

@[rep_depth krein] theorem canonicalNeutralForm_eq_two_smul_canonicalNeutralFormUnscaled :
    canonicalNeutralForm (E := E) = (2 : ℝ) • canonicalNeutralFormUnscaled (E := E) := by
  ext X
  simp [canonicalNeutralFormUnscaled]

@[rep_depth krein, simp] theorem canonicalNeutralForm_fst_zero
    (ξ : Module.Dual ℝ E) :
    canonicalNeutralForm (E := E) (0, ξ) = 0 := by
  simp [canonicalNeutralForm_apply]

@[rep_depth krein, simp] theorem canonicalNeutralForm_snd_zero
    (x : E) :
    canonicalNeutralForm (E := E) (x, 0) = 0 := by
  simp [canonicalNeutralForm_apply]

@[rep_depth krein, simp] theorem canonicalNeutralFormUnscaled_fst_zero
    (ξ : Module.Dual ℝ E) :
    canonicalNeutralFormUnscaled (E := E) (0, ξ) = 0 := by
  simp [canonicalNeutralFormUnscaled_apply]

@[rep_depth krein, simp] theorem canonicalNeutralFormUnscaled_snd_zero
    (x : E) :
    canonicalNeutralFormUnscaled (E := E) (x, 0) = 0 := by
  simp [canonicalNeutralFormUnscaled_apply]

/-- Clifford algebra over the canonical neutral phase-space form. -/
@[rep_depth operator]
abbrev NeutralPhaseClifford (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  CliffordAlgebra (canonicalNeutralForm (E := E))

end Core

end InfoGeometry.Clifford.NeutralPhaseSpaceCore
