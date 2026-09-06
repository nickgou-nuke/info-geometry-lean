import InfoGeometry.Algebra.CommutingNilpotentSum
import InfoGeometry.Categorical.LogEndModuleCategory

/-!
# InfoGeometry.Categorical.LogEndModuleNilpotentClosure

Tensor-stability theorem for finite logarithmic nilpotency.

For logarithmic endomorphism objects `X,Y`, if

`X.N ^ m = 0` and `Y.N ^ n = 0`,

then the primitive tensor endomorphism

`N_{X⊗Y} = X.N ⊗ id + id ⊗ Y.N`

satisfies

`N_{X⊗Y} ^ (m+n-1) = 0`.

This is the general owner theorem behind the rank-two × rank-two cube-zero
calculation.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogEndModuleNilpotentClosure

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Algebra.CommutingNilpotentSum
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule

universe u v

variable {𝕜 : Type u} [Field 𝕜]

/-- Left tensor-leg extension of an endomorphism. -/
def leftTensorEnd (X Y : LogEndModule 𝕜) :
    Module.End 𝕜 (X ⊗[𝕜] Y) :=
  TensorProduct.map X.N (LinearMap.id : Module.End 𝕜 Y)

/-- Right tensor-leg extension of an endomorphism. -/
def rightTensorEnd (X Y : LogEndModule 𝕜) :
    Module.End 𝕜 (X ⊗[𝕜] Y) :=
  TensorProduct.map (LinearMap.id : Module.End 𝕜 X) Y.N

/-- Mixed tensor endomorphism `N_X ⊗ N_Y`.  This is the nilpotent cross term
that appears in finite logarithmic exchange / monodromy readouts. -/
def crossTensorEnd (X Y : LogEndModule 𝕜) :
    Module.End 𝕜 (X ⊗[𝕜] Y) :=
  TensorProduct.map X.N Y.N

/-- The two tensor-leg endomorphisms commute. -/
theorem leftTensorEnd_commute_rightTensorEnd (X Y : LogEndModule 𝕜) :
    Commute (leftTensorEnd X Y) (rightTensorEnd X Y) := by
  apply Commute.eq
  ext x y
  simp [leftTensorEnd, rightTensorEnd, TensorProduct.map_tmul]

/-- Powers of the left tensor-leg action remain on the left factor. -/
theorem leftTensorEnd_pow (X Y : LogEndModule 𝕜) (m : ℕ) :
    (leftTensorEnd X Y) ^ m =
      TensorProduct.map (X.N ^ m)
        (LinearMap.id : Module.End 𝕜 Y) := by
  induction m with
  | zero =>
      ext x y
      simp [leftTensorEnd]
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      ext x y
      simp [leftTensorEnd, TensorProduct.map_tmul]

/-- Powers of the right tensor-leg action remain on the right factor. -/
theorem rightTensorEnd_pow (X Y : LogEndModule 𝕜) (n : ℕ) :
    (rightTensorEnd X Y) ^ n =
      TensorProduct.map (LinearMap.id : Module.End 𝕜 X)
        (Y.N ^ n) := by
  induction n with
  | zero =>
      ext x y
      simp [rightTensorEnd]
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      ext x y
      simp [rightTensorEnd, TensorProduct.map_tmul]

/-- Nilpotence on the left factor lifts to the left tensor-leg action. -/
theorem leftTensorEnd_pow_eq_zero
    (X Y : LogEndModule 𝕜) (m : ℕ)
    (hX : X.N ^ m = 0) :
    (leftTensorEnd X Y) ^ m = 0 := by
  rw [leftTensorEnd_pow, hX]
  ext x y
  simp

/-- Nilpotence on the right factor lifts to the right tensor-leg action. -/
theorem rightTensorEnd_pow_eq_zero
    (X Y : LogEndModule 𝕜) (n : ℕ)
    (hY : Y.N ^ n = 0) :
    (rightTensorEnd X Y) ^ n = 0 := by
  rw [rightTensorEnd_pow, hY]
  ext x y
  simp

/-- The tensor object's distinguished endomorphism is the sum of its two
commuting tensor-leg extensions. -/
theorem tensorObj_N_eq_left_add_right (X Y : LogEndModule 𝕜) :
    (tensorObj X Y).N = leftTensorEnd X Y + rightTensorEnd X Y := by
  rfl

/-- If both logarithmic directions are square-zero, then the mixed cross term
`N_X ⊗ N_Y` is itself square-zero. -/
theorem crossTensorEnd_sq_eq_zero_of_sq_zero
    (X Y : LogEndModule 𝕜)
    (hX : X.N ^ 2 = 0) (hY : Y.N ^ 2 = 0) :
    (crossTensorEnd X Y) ^ 2 = 0 := by
  ext x y
  have hx := congrArg (fun T : Module.End 𝕜 X => T x) hX
  have hy := congrArg (fun T : Module.End 𝕜 Y => T y) hY
  simp [crossTensorEnd, pow_two, Module.End.mul_eq_comp,
    LinearMap.comp_apply, TensorProduct.map_tmul] at hx hy ⊢
  simp [hx, hy]

/-- For square-zero factors, applying the mixed cross term after the primitive
tensor nilpotent gives zero. -/
theorem crossTensorEnd_comp_tensorObj_N_eq_zero
    (X Y : LogEndModule 𝕜)
    (hX : X.N ^ 2 = 0) (hY : Y.N ^ 2 = 0) :
    (crossTensorEnd X Y).comp (tensorObj X Y).N = 0 := by
  ext x y
  have hx := congrArg (fun T : Module.End 𝕜 X => T x) hX
  have hy := congrArg (fun T : Module.End 𝕜 Y => T y) hY
  simp [crossTensorEnd, tensorObj_N_tmul, LinearMap.comp_apply,
    TensorProduct.map_tmul, pow_two, Module.End.mul_eq_comp] at hx hy ⊢
  simp [hx, hy]

/-- For square-zero factors, applying the primitive tensor nilpotent after the
mixed cross term also gives zero. -/
theorem tensorObj_N_comp_crossTensorEnd_eq_zero
    (X Y : LogEndModule 𝕜)
    (hX : X.N ^ 2 = 0) (hY : Y.N ^ 2 = 0) :
    (tensorObj X Y).N.comp (crossTensorEnd X Y) = 0 := by
  ext x y
  have hx := congrArg (fun T : Module.End 𝕜 X => T x) hX
  have hy := congrArg (fun T : Module.End 𝕜 Y => T y) hY
  simp [crossTensorEnd, tensorObj_N_tmul, LinearMap.comp_apply,
    TensorProduct.map_tmul, pow_two, Module.End.mul_eq_comp] at hx hy ⊢
  simp [hx, hy]

/-- Hence the mixed square-zero cross term commutes with the primitive
logarithmic tensor endomorphism.  In fact both ordered products vanish. -/
theorem crossTensorEnd_commute_tensorObj_N_of_sq_zero
    (X Y : LogEndModule 𝕜)
    (hX : X.N ^ 2 = 0) (hY : Y.N ^ 2 = 0) :
    Commute (crossTensorEnd X Y) (tensorObj X Y).N := by
  apply Commute.eq
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    crossTensorEnd_comp_tensorObj_N_eq_zero X Y hX hY,
    tensorObj_N_comp_crossTensorEnd_eq_zero X Y hX hY]

/-- General logarithmic tensor-closure bound.

If `X.N^m=0` and `Y.N^n=0`, then
`N_(X⊗Y)^(m+n-1)=0`. -/
theorem tensorObj_N_pow_add_sub_one_eq_zero
    (X Y : LogEndModule 𝕜) (m n : ℕ)
    (hX : X.N ^ m = 0)
    (hY : Y.N ^ n = 0) :
    (tensorObj X Y).N ^ (m + n - 1) = 0 := by
  rw [tensorObj_N_eq_left_add_right]
  exact add_pow_eq_zero_of_commute_of_pow_eq_zero
    (leftTensorEnd X Y) (rightTensorEnd X Y) m n
    (leftTensorEnd_commute_rightTensorEnd X Y)
    (leftTensorEnd_pow_eq_zero X Y m hX)
    (rightTensorEnd_pow_eq_zero X Y n hY)

/-- Rank-two × rank-two specialization: square-zero factors give a cube-zero
tensor logarithmic endomorphism. -/
theorem tensorObj_cube_zero_of_sq_zero
    (X Y : LogEndModule 𝕜)
    (hX : X.N ^ 2 = 0)
    (hY : Y.N ^ 2 = 0) :
    (tensorObj X Y).N ^ 3 = 0 := by
  simpa using
    (tensorObj_N_pow_add_sub_one_eq_zero X Y 2 2 hX hY)

end InfoGeometry.Categorical.LogEndModuleNilpotentClosure
