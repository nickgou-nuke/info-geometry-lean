/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwoTwistorPlucker
import InfoGeometry.Twistor.TwistorFrameCovariance

/-!
# The flat infinity twistor on the native Penrose carrier

The infinity twistor is a degenerate alternating form, equivalently a linear
map to the dual. Its evaluation on two twistors reads the lower-spinor minor
`p23`. Its radical is the upper-spinor plane; its projectivization is the
distinguished twistor line representing the vertex of conformal infinity.
This form is not an invertible transformation exchanging zero and infinity.

Translations and determinant-one spinor frame changes preserve the form.
These are explicit preservation theorems, not a classification of the full
real conformal stabilizer as the Poincaré group.
-/

namespace InfoGeometry.Twistor.InfinityTwistor

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPlucker
open InfoGeometry.Twistor.TwistorFrameCovariance

/-- Native alternating two-form obtained by pulling back the spinor determinant. -/
def infinityAlternating : Twistor4 [⋀^Fin 2]→ₗ[ℂ] ℂ :=
  Matrix.detRowAlternating.compLinearMap (LinearMap.snd ℂ Spinor2 Spinor2)

/-- The covariant infinity twistor, as an operator into the actual linear dual. -/
def infinityTwistor : Twistor4 →ₗ[ℂ] Module.Dual ℂ Twistor4 where
  toFun Z :=
    { toFun := fun W => Z.2 0 * W.2 1 - Z.2 1 * W.2 0
      map_add' := by intros; simp [mul_add]; ring
      map_smul' := by intros; simp [smul_eq_mul]; ring }
  map_add' Z V := by
    apply LinearMap.ext
    intro W
    change (Z.2 0 + V.2 0) * W.2 1 - (Z.2 1 + V.2 1) * W.2 0 =
      (Z.2 0 * W.2 1 - Z.2 1 * W.2 0) + (V.2 0 * W.2 1 - V.2 1 * W.2 0)
    ring
  map_smul' c Z := by
    apply LinearMap.ext
    intro W
    change (c * Z.2 0) * W.2 1 - (c * Z.2 1) * W.2 0 =
      c * (Z.2 0 * W.2 1 - Z.2 1 * W.2 0)
    ring

@[simp] theorem infinityTwistor_apply (Z W : Twistor4) :
    infinityTwistor Z W = Z.2 0 * W.2 1 - Z.2 1 * W.2 0 := rfl

/-- The curried operator and the native alternating form are the same form. -/
theorem infinityAlternating_pair (Z W : Twistor4) :
    infinityAlternating ![Z, W] = infinityTwistor Z W := by
  change Matrix.det ![Z.2, W.2] = _
  exact Matrix.det_fin_two ![Z.2, W.2]

@[simp] theorem infinityTwistor_self (Z : Twistor4) :
    infinityTwistor Z Z = 0 := by simp [infinityTwistor]; ring

theorem infinityTwistor_swap (Z W : Twistor4) :
    infinityTwistor W Z = -infinityTwistor Z W := by
  simp [infinityTwistor]; ring

/-- Contraction with the infinity form is precisely the existing `p23` minor. -/
theorem infinityTwistor_eq_plucker_p23 (Z W : Twistor4) :
    infinityTwistor Z W = (twistorPairPlucker Z W).p23 := rfl

/-- The radical is exactly the upper-spinor plane, not the zero subspace. -/
theorem infinityTwistor_radical (Z : Twistor4) :
    infinityTwistor Z = 0 ↔ Z.2 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Module.Dual ℂ Twistor4 => f (0, ![0, 1])) h
    have h1 := congrArg (fun f : Module.Dual ℂ Twistor4 => f (0, ![1, 0])) h
    simp [infinityTwistor] at h0 h1
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    apply LinearMap.ext
    intro W
    simp [infinityTwistor, h]

theorem ker_infinityTwistor :
    LinearMap.ker infinityTwistor =
      LinearMap.ker (LinearMap.snd ℂ Spinor2 Spinor2) := by
  ext Z
  exact infinityTwistor_radical Z

/-- A concrete nonzero radical vector prevents treating the form as an inverse. -/
theorem infinityTwistor_not_injective : ¬Function.Injective infinityTwistor := by
  intro h
  have hz : infinityTwistor ((![1, 0] : Spinor2), (0 : Spinor2)) = 0 :=
    (infinityTwistor_radical _).2 rfl
  have he := h (hz.trans (map_zero infinityTwistor).symm)
  have := congrArg (fun Z : Twistor4 => Z.1 0) he
  norm_num at this

/-- Translation acts on the native incidence carrier with its owner's factor `i`. -/
def translation (A : ComplexSpacetime) : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (Z.1 + Complex.I • omegaLinearMap A Z.2, Z.2)
  invFun Z := (Z.1 - Complex.I • omegaLinearMap A Z.2, Z.2)
  left_inv Z := by ext <;> simp
  right_inv Z := by ext <;> simp
  map_add' Z W := by
    ext <;> simp [map_add, smul_add]
    abel
  map_smul' c Z := by ext <;> simp [map_smul, smul_add, smul_smul, mul_comm]

@[simp] theorem infinityTwistor_translation (A : ComplexSpacetime) (Z W : Twistor4) :
    infinityTwistor (translation A Z) (translation A W) = infinityTwistor Z W := rfl

theorem translation_incidence (A X : ComplexSpacetime) (π : Spinor2) :
    translation A (incidenceLinearMap X π) = incidenceLinearMap (X + A) π := by
  ext <;> simp [translation, incidenceLinearMap, omegaLinearMap, smul_add]

/-- The weight under a general lower-spinor frame is its determinant. -/
theorem infinityTwistor_frameAction (A : ComplexSpacetime) (Z W : Twistor4) :
    infinityTwistor (twistorFrameAction A Z) (twistorFrameAction A W) =
      A.det * infinityTwistor Z W := by
  simp [infinityTwistor, twistorFrameAction, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- Determinant-one frame changes preserve the infinity form. -/
theorem infinityTwistor_frameAction_det_one (A : ComplexSpacetime)
    (hA : A.det = 1) (Z W : Twistor4) :
    infinityTwistor (twistorFrameAction A Z) (twistorFrameAction A W) =
      infinityTwistor Z W := by rw [infinityTwistor_frameAction, hA, one_mul]

end InfoGeometry.Twistor.InfinityTwistor
