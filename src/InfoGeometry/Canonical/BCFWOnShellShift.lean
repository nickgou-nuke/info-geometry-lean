import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open Complex

section BCFW

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (B : LinearMap.BilinForm ℂ V)

/-- The shifted momentum `p_i(z) = p_i + z q`. -/
def shiftedPi (pi q : V) (z : ℂ) : V := pi + z • q

/-- The shifted momentum `p_j(z) = p_j - z q`. -/
def shiftedPj (pj q : V) (z : ℂ) : V := pj - z • q

/-- Bilinearity in the first argument, exposed as a reusable consequence of
the native `BilinForm` structure. -/
@[simp] lemma bilin_add_left (x y w : V) :
    B (x + y) w = B x w + B y w := by
  exact congrArg (fun f : V →ₗ[ℂ] ℂ => f w) (B.map_add x y)

@[simp] lemma bilin_smul_left (c : ℂ) (x w : V) :
    B (c • x) w = c * B x w := by
  exact congrArg (fun f : V →ₗ[ℂ] ℂ => f w) (B.map_smul c x)

@[simp] lemma bilin_add_right (x y w : V) :
    B x (y + w) = B x y + B x w := by
  exact (B x).map_add y w

@[simp] lemma bilin_smul_right (c : ℂ) (x y : V) :
    B x (c • y) = c * B x y := by
  exact (B x).map_smul c y

lemma bilin_sub_left (x y w : V) :
    B (x - y) w = B x w - B y w := by
  rw [sub_eq_add_neg, bilin_add_left]
  simp
  ring

lemma bilin_sub_right (hB : B.IsSymm) (x y w : V) :
    B x (y - w) = B x y - B x w := by
  rw [hB.eq x (y - w), bilin_sub_left, hB.eq y x, hB.eq w x]

/-- A BCFW shift preserves the left momentum's nullity. -/
theorem bcfw_shift_left_null (hB : B.IsSymm) (pi q : V) (z : ℂ)
    (hpi : B pi pi = 0) (hq : B q q = 0) (hpiq : B pi q = 0) :
    B (shiftedPi pi q z) (shiftedPi pi q z) = 0 := by
  calc
    B (shiftedPi pi q z) (shiftedPi pi q z) =
        B pi pi + z * B pi q + z * B q pi + z ^ 2 * B q q := by
      simp [shiftedPi]
      ring
    _ = 0 := by simp [hpi, hpiq, hB.eq q pi, hq]

/-- A BCFW shift preserves the right momentum's nullity. -/
theorem bcfw_shift_right_null (hB : B.IsSymm) (pj q : V) (z : ℂ)
    (hpj : B pj pj = 0) (hq : B q q = 0) (hpjq : B pj q = 0) :
    B (shiftedPj pj q z) (shiftedPj pj q z) = 0 := by
  calc
    B (shiftedPj pj q z) (shiftedPj pj q z) =
        B pj pj - z * B pj q - z * B q pj + z ^ 2 * B q q := by
      simp [shiftedPj, bilin_sub_right B hB]
      ring
    _ = 0 := by simp [hpj, hpjq, hB.eq q pj, hq]

/-- Total momentum is conserved by the opposite shifts. -/
theorem bcfw_shift_momentum_conservation (pi pj q : V) (z : ℂ) :
    shiftedPi pi q z + shiftedPj pj q z = pi + pj := by
  dsimp [shiftedPi, shiftedPj]
  abel

/-- Channel momentum `P_I(z) = P_I + z q`. -/
def shiftedChannel (PI q : V) (z : ℂ) : V := PI + z • q

/-- The shifted channel quadratic is affine in the shift parameter. -/
lemma shiftedChannel_sq (hB : B.IsSymm) (PI q : V) (z : ℂ)
    (hq : B q q = 0) :
    B (shiftedChannel PI q z) (shiftedChannel PI q z) =
      B PI PI + z * (2 * B PI q) := by
  simp [shiftedChannel, hB.eq q PI, hq]
  ring

/-- If the affine channel slope is nonzero, the unique affine root puts the
shifted channel on the null quadric. -/
theorem bcfw_channel_goes_onShell (hB : B.IsSymm) (PI q : V)
    (hq : B q q = 0) (hslope : 2 * B PI q ≠ 0) :
    B (shiftedChannel PI q (-B PI PI / (2 * B PI q)))
      (shiftedChannel PI q (-B PI PI / (2 * B PI q))) = 0 := by
  rw [shiftedChannel_sq B hB PI q _ hq]
  have hmul :
      (-B PI PI / (2 * B PI q)) * (2 * B PI q) = -B PI PI :=
    div_mul_cancel₀ _ hslope
  rw [hmul]
  ring

end BCFW

end InfoGeometry.Canonical
