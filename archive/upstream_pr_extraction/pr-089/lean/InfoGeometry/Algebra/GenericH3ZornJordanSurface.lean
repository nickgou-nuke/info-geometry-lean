import InfoGeometry.Algebra.H3ZornCubicOperators

/-!
# Generic cubic Jordan surface for `H3Zorn`

This is the coefficient-field-independent predecessor of the real-only
`candidateJordanMul`.  It exposes the same cubic construction over any field
and therefore provides the correct carrier for exact rational certificates.
No claim about a basis or a rank certificate is made here.
-/

namespace InfoGeometry.Algebra

open H3Zorn

variable {R : Type*} [Field R]

/-- The cubic Jordan product induced by the generic `H3Zorn` trilinear form. -/
noncomputable def cubicJordanMul (X Y : H3Zorn R) : H3Zorn R :=
  (2 : R)⁻¹ • H3Zorn.T X 1 Y

@[simp] theorem cubicJordanMul_comm (X Y : H3Zorn R) :
    cubicJordanMul X Y = cubicJordanMul Y X := by
  simp only [cubicJordanMul, H3Zorn.T_symm_outer]

theorem cubicJordanMul_add_left (X₁ X₂ Y : H3Zorn R) :
    cubicJordanMul (X₁ + X₂) Y =
      cubicJordanMul X₁ Y + cubicJordanMul X₂ Y := by
  simp only [cubicJordanMul, H3Zorn.T_add_left, smul_add]

theorem cubicJordanMul_add_right (X Y₁ Y₂ : H3Zorn R) :
    cubicJordanMul X (Y₁ + Y₂) =
      cubicJordanMul X Y₁ + cubicJordanMul X Y₂ := by
  rw [cubicJordanMul_comm, cubicJordanMul_add_left]
  rw [cubicJordanMul_comm Y₁ X, cubicJordanMul_comm Y₂ X]

theorem cubicJordanMul_smul_left (r : R) (X Y : H3Zorn R) :
    cubicJordanMul (r • X) Y = r • cubicJordanMul X Y := by
  simp only [cubicJordanMul, H3Zorn.T_smul_left, smul_smul]
  module

theorem cubicJordanMul_smul_right (r : R) (X Y : H3Zorn R) :
    cubicJordanMul X (r • Y) = r • cubicJordanMul X Y := by
  rw [cubicJordanMul_comm, cubicJordanMul_smul_left]
  rw [cubicJordanMul_comm Y X]

/-- The pointwise commutator of two cubic Jordan left multiplications.  This
is the coefficient-field-independent action used by exact certificates. -/
noncomputable def cubicJordanInnerAction (A B X : H3Zorn R) : H3Zorn R :=
  cubicJordanMul A (cubicJordanMul B X) -
    cubicJordanMul B (cubicJordanMul A X)

theorem cubicJordanInnerAction_add (A B X Y : H3Zorn R) :
    cubicJordanInnerAction A B (X + Y) =
      cubicJordanInnerAction A B X + cubicJordanInnerAction A B Y := by
  simp only [cubicJordanInnerAction, cubicJordanMul_add_right]
  abel

theorem cubicJordanInnerAction_smul (r : R) (A B X : H3Zorn R) :
    cubicJordanInnerAction A B (r • X) =
      r • cubicJordanInnerAction A B X := by
  simp only [cubicJordanInnerAction, cubicJordanMul_smul_right, smul_sub]

theorem cubicJordanInnerAction_apply (A B X : H3Zorn R) :
    cubicJordanInnerAction A B X =
      cubicJordanMul A (cubicJordanMul B X) -
        cubicJordanMul B (cubicJordanMul A X) := rfl

end InfoGeometry.Algebra
