import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.Canonical.OrthogonalGroup55

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.AffineOrthogonal55Glide

open InfoGeometry.Canonical.O55Representation

abbrev V55 : Type _ := Fin 10 → ℝ

def orthogonal55LinearEquiv (g : OrthogonalGroup55) : V55 ≃ₗ[ℝ] V55 where
  toFun := ((g : GL10) : O55Matrix).mulVec
  invFun := (((g⁻¹ : OrthogonalGroup55) : GL10) : O55Matrix).mulVec
  left_inv := by
    intro x
    rw [Matrix.mulVec_mulVec]
    rw [← Units.val_mul]
    simp
  right_inv := by
    intro x
    rw [Matrix.mulVec_mulVec]
    rw [← Units.val_mul]
    simp
  map_add' := by
    intro x y
    exact Matrix.mulVec_add _ _ _
  map_smul' := by
    intro c x
    exact Matrix.mulVec_smul _ _ _

def orthogonal55MulAut (g : OrthogonalGroup55) :
    MulAut (Multiplicative V55) :=
  (orthogonal55LinearEquiv g).toAddEquiv.toMultiplicative

def orthogonal55Action :
    OrthogonalGroup55 →* MulAut (Multiplicative V55) where
  toFun := orthogonal55MulAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    change ((1 : GL10) : O55Matrix).mulVec (x : V55) = x
    exact Matrix.one_mulVec _
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change ((g * h : GL10) : O55Matrix).mulVec (x : V55) =
      ((g : GL10) : O55Matrix).mulVec
        (((h : GL10) : O55Matrix).mulVec (x : V55))
    have hgh :
        ((g.1 * h.1 : GL10) : O55Matrix) =
          (g.1 : O55Matrix) * (h.1 : O55Matrix) := by
      simpa using (Units.val_mul g.1 h.1)
    rw [hgh, Matrix.mulVec_mulVec]

abbrev AffineOrthogonal55Native : Type _ :=
  Multiplicative V55 ⋊[orthogonal55Action] OrthogonalGroup55

theorem affineNative_mul_coordinates
    (a b : AffineOrthogonal55Native) :
    a * b =
      SemidirectProduct.mk
        (a.left * orthogonal55Action a.right b.left) (a.right * b.right) := by
  exact SemidirectProduct.mul_def a b

def affineNativeGlide (t : V55) (r : OrthogonalGroup55) :
    AffineOrthogonal55Native :=
  SemidirectProduct.mk (Multiplicative.ofAdd t) r

theorem affineNativeGlide_square_general
    (t : V55) (r : OrthogonalGroup55) :
    affineNativeGlide t r * affineNativeGlide t r =
    SemidirectProduct.mk
        (Multiplicative.ofAdd
          (t + ((r : GL10) : O55Matrix).mulVec t))
        (r * r) := by
  rw [SemidirectProduct.mul_def]
  rfl

theorem affineNativeGlide_square
    (t : V55) (r : OrthogonalGroup55)
    (hr : r * r = 1)
    (ht : ((r : GL10) : O55Matrix).mulVec t = t) :
    affineNativeGlide t r * affineNativeGlide t r =
      SemidirectProduct.mk (Multiplicative.ofAdd (2 • t)) 1 := by
  apply SemidirectProduct.ext
  · change t + ((r : GL10) : O55Matrix).mulVec t = 2 • t
    rw [ht]
    ext i
    simp
    ring
  · exact hr

theorem affineNativeGlide_square_anti_fixed
    (t : V55) (r : OrthogonalGroup55)
    (hr : r * r = 1)
    (ht : ((r : GL10) : O55Matrix).mulVec t = -t) :
    affineNativeGlide t r * affineNativeGlide t r = 1 := by
  rw [affineNativeGlide_square_general]
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd
      (t + ((r : GL10) : O55Matrix).mulVec t) = 1
    rw [ht]
    change Multiplicative.ofAdd (t + -t) = Multiplicative.ofAdd 0
    simp
  · simpa using hr

theorem affineNative_conj_translation
    (t : V55) (r : OrthogonalGroup55) :
    affineNativeGlide 0 r * affineNativeGlide t 1 *
        (affineNativeGlide 0 r)⁻¹ =
      affineNativeGlide
        (((r : GL10) : O55Matrix).mulVec t) 1 := by
  apply SemidirectProduct.ext
  · simp [affineNativeGlide, orthogonal55Action]
    rfl
  · simp [affineNativeGlide, orthogonal55Action]

end InfoGeometry.Canonical.AffineOrthogonal55Glide
