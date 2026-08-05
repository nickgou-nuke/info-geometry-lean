import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.Canonical.AffineOrthogonal55Glide

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.AffineOrthogonal55Glide

open InfoGeometry.Canonical.O55Representation

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

abbrev AffineOrthogonal55Native :=
  Multiplicative V55 ⋊[orthogonal55Action] OrthogonalGroup55

theorem affineNative_mul_coordinates
    (a b : AffineOrthogonal55Native) :
    a * b =
      SemidirectProduct.mk
        (a.left * orthogonal55Action a.right b.left) (a.right * b.right) := by
  rfl

def affineNativeGlide (t : V55) (r : OrthogonalGroup55) :
    AffineOrthogonal55Native :=
  SemidirectProduct.mk (Multiplicative.ofAdd t) r

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

end InfoGeometry.Canonical.AffineOrthogonal55Glide
