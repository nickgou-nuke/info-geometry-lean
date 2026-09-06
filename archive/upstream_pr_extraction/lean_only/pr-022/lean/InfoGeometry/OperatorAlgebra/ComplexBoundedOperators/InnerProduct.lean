import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Complex inner-product adapters for AFP `Complex_Inner_Product0`

AFP's `Complex_Inner_Product0` builds the complex inner-product hierarchy and
basic sesquilinear/norm inequalities from first principles.

In Lean/mathlib this is native `InnerProductSpace ℂ E`.  This file exposes
small AFP-name-compatible adapter lemmas for the complex bounded-operator
corridor; all proofs are direct wrappers around mathlib theorems.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace InnerProduct

open scoped InnerProductSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Sesquilinear inner-product laws -/

theorem cinner_commute (x y : E) :
    ⟪x, y⟫_ℂ = star ⟪y, x⟫_ℂ := by
  simpa using (inner_conj_symm (𝕜 := ℂ) x y)

theorem cinner_add_left (x y z : E) :
    ⟪x + y, z⟫_ℂ = ⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ :=
  inner_add_left x y z

theorem cinner_add_right (x y z : E) :
    ⟪x, y + z⟫_ℂ = ⟪x, y⟫_ℂ + ⟪x, z⟫_ℂ :=
  inner_add_right x y z

theorem cinner_smul_left (c : ℂ) (x y : E) :
    ⟪c • x, y⟫_ℂ = star c * ⟪x, y⟫_ℂ :=
  inner_smul_left x y c

theorem cinner_smul_right (c : ℂ) (x y : E) :
    ⟪x, c • y⟫_ℂ = c * ⟪x, y⟫_ℂ :=
  inner_smul_right x y c

theorem cinner_diff_left (x y z : E) :
    ⟪x - y, z⟫_ℂ = ⟪x, z⟫_ℂ - ⟪y, z⟫_ℂ := by
  simp [sub_eq_add_neg, cinner_add_left]

theorem cinner_diff_right (x y z : E) :
    ⟪x, y - z⟫_ℂ = ⟪x, y⟫_ℂ - ⟪x, z⟫_ℂ := by
  simp [sub_eq_add_neg, cinner_add_right]

theorem cinner_eq_flip {x y z w : E} :
    (⟪x, y⟫_ℂ = ⟪z, w⟫_ℂ) ↔ (⟪y, x⟫_ℂ = ⟪w, z⟫_ℂ) := by
  constructor <;> intro h
  · simpa [cinner_commute] using congrArg star h
  · simpa [cinner_commute] using congrArg star h

@[simp]
theorem im_cinner_self (x : E) :
    Complex.im ⟪x, x⟫_ℂ = 0 :=
  inner_self_im x

theorem cinner_smul_real_left (r : ℝ) (x y : E) :
    ⟪r • x, y⟫_ℂ = (r : ℂ) * ⟪x, y⟫_ℂ := by
  simpa [Algebra.smul_def] using inner_smul_real_left (𝕜 := ℂ) x y r

theorem cinner_smul_real_right (r : ℝ) (x y : E) :
    ⟪x, r • y⟫_ℂ = (r : ℂ) * ⟪x, y⟫_ℂ := by
  simpa [Algebra.smul_def] using inner_smul_real_right (𝕜 := ℂ) x y r

/-! ## Nondegeneracy and norm identities -/

theorem cinner_all_right_zero_iff (x : E) :
    (∀ u : E, ⟪x, u⟫_ℂ = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact ext_inner_right ℂ (x := x) (y := 0) (by intro u; simpa using h u)
  · intro hx u
    simp [hx]

theorem cinner_all_left_zero_iff (x : E) :
    (∀ u : E, ⟪u, x⟫_ℂ = 0) ↔ x = 0 := by
  constructor
  · intro h
    exact ext_inner_left ℂ (x := x) (y := 0) (by intro u; simpa using h u)
  · intro hx u
    simp [hx]

theorem re_cinner_self_pos_iff (x : E) :
    0 < Complex.re ⟪x, x⟫_ℂ ↔ x ≠ 0 :=
  re_inner_self_pos

theorem cinner_self_eq_norm_sq (x : E) :
    ⟪x, x⟫_ℂ = (‖x‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K x

theorem cinner_self_eq_zero_iff (x : E) :
    ⟪x, x⟫_ℂ = 0 ↔ x = 0 :=
  inner_self_eq_zero

theorem cinner_extensionality {ψ φ : E}
    (h : ∀ γ : E, ⟪γ, ψ⟫_ℂ = ⟪γ, φ⟫_ℂ) :
    ψ = φ :=
  ext_inner_left ℂ h

/-! ## Cauchy--Schwarz and polarization -/

theorem norm_cinner_le_norm (x y : E) :
    ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

theorem cinner_mul_cinner_self_le (x y : E) :
    ‖⟪x, y⟫_ℂ‖ * ‖⟪y, x⟫_ℂ‖ ≤
      Complex.re ⟪x, x⟫_ℂ * Complex.re ⟪y, y⟫_ℂ :=
  inner_mul_inner_self_le x y

theorem polar_identity (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * Complex.re ⟪x, y⟫_ℂ := by
  rw [norm_add_sq]
  ring

theorem polar_identity_minus (x y : E) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * Complex.re ⟪x, y⟫_ℂ := by
  rw [norm_sub_sq]
  ring

theorem parallelogram_law (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [polar_identity, polar_identity_minus]
  ring

theorem pythagorean_theorem {x y : E} (hxy : ⟪x, y⟫_ℂ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [polar_identity, hxy]
  simp

theorem sum_cinner {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → E) (g : κ → E) :
    ⟪∑ i in s, f i, ∑ j in t, g j⟫_ℂ =
      ∑ i in s, ∑ j in t, ⟪f i, g j⟫_ℂ := by
  simp [sum_inner, inner_sum]

/-- Complex polarization identity in mathlib's native form. -/
theorem cinner_polarization (x y : E) :
    ⟪x, y⟫_ℂ =
      ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
          (((‖x - Complex.I • y‖ : ℂ) ^ 2 -
              (‖x + Complex.I • y‖ : ℂ) ^ 2) * Complex.I)) / 4 :=
  inner_eq_sum_norm_sq_div_four x y

end InnerProduct
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
