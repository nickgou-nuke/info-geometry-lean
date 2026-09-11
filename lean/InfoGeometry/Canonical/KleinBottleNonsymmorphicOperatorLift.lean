import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nonsymmorphic cubic glide lift

The translation, cubic charge, and glide are kept as separate operators.  The
only order-six conclusion proved here is the elementary consequence of
`glide² = translation` and `translation³ = 1`; no geometric or analytic lift
is inferred beyond these exact hypotheses.
-/

namespace InfoGeometry.Canonical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure CubicGlideLift (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  cubicCharge : V ≃ₗ[K] V
  axisTranslation : V ≃ₗ[K] V
  glide : V ≃ₗ[K] V
  charge_cube : cubicCharge ^ 3 = 1
  axis_cube : axisTranslation ^ 3 = 1
  glide_square : glide ^ 2 = axisTranslation
  glide_conj_charge : glide * cubicCharge * glide.symm = cubicCharge.symm

theorem glide_pow_six_eq_one (D : CubicGlideLift K V) :
    D.glide ^ 6 = 1 := by
  calc
    D.glide ^ 6 = D.glide ^ (2 * 3) := by norm_num
    _ = (D.glide ^ 2) ^ 3 := by rw [pow_mul]
    _ = D.axisTranslation ^ 3 := by rw [D.glide_square]
    _ = 1 := D.axis_cube

theorem glide_square_eq_axisTranslation (D : CubicGlideLift K V) :
    D.glide ^ 2 = D.axisTranslation :=
  D.glide_square

end InfoGeometry.Canonical
