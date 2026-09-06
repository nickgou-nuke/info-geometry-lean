import proofs.KleinBottleSixfoldCyclotomic
import Mathlib.Data.ZMod.Basic

/-!
# Six-state internal bundle data over a Klein glide

This file isolates the fibre theorem required by a future topological Klein
Brillouin quotient.  The base is left abstract: an involution `τ` represents
the glide on the quotient, and matrix-valued families descend when they obey
the stated equivariance law.
-/

noncomputable section

namespace KleinSixStateBundle

open TwoSheetThreeColorWeyl
open KleinBottleSixfoldCyclotomic

abbrev Operator := M6C

/-- Orientation-reversing sheet/family action `J ⊗ R`. -/
def theta : Operator := internalGlide

/-- Sixfold sheet/family triality `Γ ⊗ X`. -/
def triality : Operator := sixfoldTriality

theorem theta_sq (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    theta * theta = (1 : Operator) :=
  (internal_klein_relations ω hω).1

/-- The fifth power is the concrete inverse certificate for the order-six
operator. -/
theorem triality_mul_fifth (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    triality * triality ^ 5 = (1 : Operator) := by
  calc
    triality * triality ^ 5 = triality ^ 6 := by
      simp [pow_succ', Matrix.mul_assoc]
    _ = 1 := sixfoldTriality_sixth ω hω

theorem triality_fifth_formula :
    triality ^ 5 = tensor sheetGamma (colorShift ^ 2) := by
  have hΓ : sheetGamma * sheetGamma = (1 : M2C) := sheet_parity.1
  have hX : colorShift ^ 3 = (1 : M3C) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [colorShift, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]
  calc
    triality ^ 5 = tensor (sheetGamma ^ 5) (colorShift ^ 5) := by
      simp [triality, sixfoldTriality, pow_succ, tensor_mul, Matrix.mul_assoc]
    _ = tensor sheetGamma (colorShift ^ 2) := by
      congr 1
      · simp [pow_succ, hΓ]
      · calc
          colorShift ^ 5 = colorShift ^ 3 * colorShift ^ 2 := by
            rw [← pow_add]
          _ = colorShift ^ 2 := by rw [hX, Matrix.one_mul]

/-- Pin/chiral refinement of the ordinary dihedral reflection law:
`Θ T Θ = -T⁻¹`, with `T⁵` serving as the concrete inverse of `T`. -/
theorem theta_triality_theta (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    theta * triality * theta = -(triality ^ 5) := by
  rcases sheet_parity with ⟨_, hJ, hJΓ⟩
  rcases color_reflection_relations ω hω with ⟨hR, hRX, _⟩
  calc
    theta * triality * theta =
        tensor (sheetFlip * sheetGamma * sheetFlip)
          (colorReflection * colorShift * colorReflection) := by
      simp [theta, triality, internalGlide, sixfoldTriality,
        tensor_mul, Matrix.mul_assoc]
    _ = tensor (-sheetGamma) (colorShift ^ 2) := by rw [hJΓ, hRX]
    _ = -(tensor sheetGamma (colorShift ^ 2)) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      simp [tensor, Matrix.kroneckerMap_apply]
    _ = -(triality ^ 5) := by rw [triality_fifth_formula]

/-! ## Hexagon-index action -/

/-- Spectral reflection `ζ₆ⁿ ↦ -ζ₆⁻ⁿ = ζ₆^(3-n)`. -/
def hexReflect (n : ZMod 6) : ZMod 6 := 3 - n

@[simp] theorem hexReflect_involutive (n : ZMod 6) :
    hexReflect (hexReflect n) = n := by
  simp [hexReflect]

theorem hexReflect_eq_parity_minus (n : ZMod 6) :
    hexReflect n = 3 + (-n) := by
  simp [hexReflect, sub_eq_add_neg]

/-! ## Abstract descent interface -/

/-- A matrix family descends through a Klein glide when its value on the
glide-related point is conjugated by the internal involution. -/
def IsGlideEquivariant {K : Type*} (τ : K → K) (H : K → Operator) : Prop :=
  ∀ k, H (τ k) = theta * H k * theta

theorem glide_equivariance_twice {K : Type*} (τ : K → K) (H : K → Operator)
    (hτ : Function.Involutive τ)
    (hH : IsGlideEquivariant τ H) (k : K) :
    H k = theta * (theta * H k * theta) * theta := by
  calc
    H k = H (τ (τ k)) := by rw [hτ k]
    _ = theta * H (τ k) * theta := hH (τ k)
    _ = theta * (theta * H k * theta) * theta := by rw [hH k]

/-- Operator form of Klein holonomy: the glide reverses propagation.  The
inverse is supplied explicitly rather than through matrix invertibility. -/
structure KleinHolonomy where
  propagation : Operator
  propagationInv : Operator
  left_inverse : propagationInv * propagation = 1
  right_inverse : propagation * propagationInv = 1
  glide_reversal : theta * propagation * theta = propagationInv

/-- The order-six triality itself yields a Pin-twisted, rather than ordinary,
Klein reversal because of the extra central sign. -/
theorem triality_pin_holonomy_packet (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    triality * triality ^ 5 = (1 : Operator) ∧
    theta * triality * theta = -(triality ^ 5) :=
  ⟨triality_mul_fifth ω hω, theta_triality_theta ω hω⟩

end KleinSixStateBundle

end noncomputable section
