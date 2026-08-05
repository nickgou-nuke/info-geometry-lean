import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.OrthogonalGroup55

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.AffineOrthogonal55Glide

open InfoGeometry.Canonical.O55Representation

abbrev V55 := Fin 10 → ℝ
abbrev AffineOrthogonal55 := V55 × OrthogonalGroup55

def affineAction (a : AffineOrthogonal55) (x : V55) : V55 :=
  a.1 + ((a.2 : GL10) : O55Matrix).mulVec x

def affineMul (a b : AffineOrthogonal55) : AffineOrthogonal55 :=
  (a.1 + ((a.2 : GL10) : O55Matrix).mulVec b.1, a.2 * b.2)

def affineOne : AffineOrthogonal55 := (0, 1)

def affineInv (a : AffineOrthogonal55) : AffineOrthogonal55 :=
  (-(((a.2⁻¹ : OrthogonalGroup55) : GL10) : O55Matrix).mulVec a.1,
    a.2⁻¹)

theorem affineMul_assoc (a b c : AffineOrthogonal55) :
    affineMul (affineMul a b) c = affineMul a (affineMul b c) := by
  apply Prod.ext
  · simp only [affineMul]
    rw [Matrix.mulVec_add]
    have hab :
        ((↑(a.2 * b.2) : GL10) : O55Matrix) =
          ((a.2 : GL10) : O55Matrix) * ((b.2 : GL10) : O55Matrix) := by
      simp
    rw [hab, Matrix.mulVec_mulVec]
    rw [← Units.val_mul]
    abel
  · simp only [affineMul]
    exact mul_assoc _ _ _

theorem affineOne_mul (a : AffineOrthogonal55) :
    affineMul affineOne a = a := by
  ext <;> simp [affineMul, affineOne]

theorem affineMul_one (a : AffineOrthogonal55) :
    affineMul a affineOne = a := by
  ext <;> simp [affineMul, affineOne]

theorem affineMul_affineInv (a : AffineOrthogonal55) :
    affineMul a (affineInv a) = affineOne := by
  apply Prod.ext
  · simp only [affineMul, affineInv, affineOne]
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
    rw [← Units.val_mul]
    simp
  · change a.2 * a.2⁻¹ = 1
    exact mul_inv_cancel a.2

theorem affineInv_mul (a : AffineOrthogonal55) :
    affineMul (affineInv a) a = affineOne := by
  apply Prod.ext
  · simp only [affineMul, affineInv, affineOne]
    simp
  · change a.2⁻¹ * a.2 = 1
    exact inv_mul_cancel a.2

instance : Group AffineOrthogonal55 where
  mul := affineMul
  one := affineOne
  inv := affineInv
  mul_assoc := affineMul_assoc
  one_mul := affineOne_mul
  mul_one := affineMul_one
  div := fun a b => affineMul a (affineInv b)
  inv_mul_cancel := affineInv_mul

theorem affineMul_action (a b : AffineOrthogonal55) (x : V55) :
    affineAction (affineMul a b) x =
      affineAction a (affineAction b x) := by
  simp only [affineAction, affineMul]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [← Units.val_mul]
  abel

theorem affineSquare_formula (t : V55) (r : OrthogonalGroup55) :
    affineMul (t, r) (t, r) =
      (t + ((r : GL10) : O55Matrix).mulVec t, r * r) := rfl

theorem affineSquare_glide
    (t : V55) (r : OrthogonalGroup55)
    (hr : r * r = 1)
    (ht : ((r : GL10) : O55Matrix).mulVec t = t) :
    affineMul (t, r) (t, r) = (2 • t, 1) := by
  rw [affineSquare_formula, hr, ht]
  congr 1
  ext i
  simp
  ring

theorem affineSquare_translation_vector
    (t : V55) (r : OrthogonalGroup55)
    (_hr : r * r = 1) :
    (affineMul (t, r) (t, r)).1 =
      t + ((r : GL10) : O55Matrix).mulVec t := by
  rfl

end InfoGeometry.Canonical.AffineOrthogonal55Glide
