/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Nondegeneracy of a mixed pairing pulled back from the canonical neutral form

For a native real bilinear map `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, the linear map
`(u,v) ↦ (u,B(-,v))` lands in the existing evaluation carrier `E × E*`.
Pulling back its canonical neutral bilinear form gives
`B u v' + B u' v`. Its nondegeneracy is equivalent to both radicals of `B`
being zero, with no symmetry or finite-dimensional hypothesis on `B`.

For square finite real matrices, the native matrix-to-bilinear equivalence
identifies this condition with a nonzero determinant. These are algebraic
statements; no differential-geometric manifold or curvature is constructed.
-/

noncomputable section

namespace InfoGeometry.Geometry.MixedPairingNondegeneracy

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- The mixed pairing supplies the covector in the existing neutral carrier. -/
def pairingToDual (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    E × F →ₗ[ℝ] PhaseSpaceCarrier E :=
  (LinearMap.fst ℝ E F).prod (B.flip.comp (LinearMap.snd ℝ E F))

@[simp] theorem pairingToDual_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (X : E × F) :
    pairingToDual B X = (X.1, B.flip X.2) := rfl

/-- Native pullback of the existing canonical neutral bilinear form. -/
def neutralPullback (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    LinearMap.BilinForm ℝ (E × F) :=
  (canonicalNeutralBilin (E := E)).compl₁₂ (pairingToDual B) (pairingToDual B)

@[simp] theorem neutralPullback_apply
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (X Y : E × F) :
    neutralPullback B X Y = B X.1 Y.2 + B Y.1 X.2 := by
  simp [neutralPullback, canonicalNeutralBilin_apply, add_comm]

theorem neutralPullback_symmetric
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (X Y : E × F) :
    neutralPullback B X Y = neutralPullback B Y X := by
  simp only [neutralPullback_apply]
  exact add_comm _ _

@[simp] theorem neutralPullback_first_half
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u u' : E) :
    neutralPullback B (u, 0) (u', 0) = 0 := by
  simp

@[simp] theorem neutralPullback_second_half
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (v v' : F) :
    neutralPullback B (0, v) (0, v') = 0 := by
  simp

@[simp] theorem neutralPullback_cross
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : E) (v : F) :
    neutralPullback B (u, 0) (0, v) = B u v := by
  simp

/-- The signed product action is transported to the existing neutral involution. -/
theorem pairingToDual_signed
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (X : E × F) :
    pairingToDual B (X.1, -X.2) = neutralParaInvolution (pairingToDual B X) := by
  simp

/-- Anti-isometry follows from the canonical neutral owner's theorem. -/
theorem neutralPullback_signed_anti_isometry
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (X Y : E × F) :
    neutralPullback B (X.1, -X.2) (Y.1, -Y.2) = -neutralPullback B X Y := by
  change canonicalNeutralBilin
      (pairingToDual B (X.1, -X.2)) (pairingToDual B (Y.1, -Y.2)) =
    -canonicalNeutralBilin (pairingToDual B X) (pairingToDual B Y)
  rw [pairingToDual_signed, pairingToDual_signed]
  exact canonicalNeutralBilin_para_anti_isometry _ _

/-- The doubled neutral form is nondegenerate exactly when the original pairing
has zero left and right radicals. `B.Nondegenerate` is Mathlib's native
conjunction of these two separation predicates. -/
theorem neutralPullback_nondegenerate_iff
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    (neutralPullback B).Nondegenerate ↔ B.Nondegenerate := by
  constructor
  · intro h
    constructor
    · intro u hu
      have hz : (u, (0 : F)) = (0 : E × F) := h.1 _ (by
        intro Y
        simpa using hu Y.2)
      exact congrArg Prod.fst hz
    · intro v hv
      have hz : ((0 : E), v) = (0 : E × F) := h.1 _ (by
        intro Y
        simpa using hv Y.1)
      exact congrArg Prod.snd hz
  · rintro ⟨hleft, hright⟩
    have hsep : (neutralPullback B).SeparatingLeft := by
      intro X hX
      apply Prod.ext
      · apply hleft X.1
        intro v
        simpa using hX ((0 : E), v)
      · apply hright X.2
        intro u
        simpa using hX (u, (0 : F))
    refine ⟨hsep, ?_⟩
    intro Y hY
    exact hsep Y (fun X => (neutralPullback_symmetric B Y X).trans (hY X))

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a full square matrix cross block, the mixed form is nondegenerate iff
the determinant of that block is nonzero. No diagonal or symmetric restriction
is imposed on the matrix. -/
theorem matrix_neutralPullback_nondegenerate_iff (C : Matrix n n ℝ) :
    (neutralPullback C.toBilin').Nondegenerate ↔ C.det ≠ 0 := by
  rw [neutralPullback_nondegenerate_iff]
  exact LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero

end Matrix

end InfoGeometry.Geometry.MixedPairingNondegeneracy
