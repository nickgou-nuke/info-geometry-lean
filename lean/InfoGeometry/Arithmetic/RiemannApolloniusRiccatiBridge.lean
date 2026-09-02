import Mathlib.Tactic
import InfoGeometry.Canonical.ComplexRiccatiSL2
/-!
# Corrected Apollonius/Riccati coordinate bridge for the Riemann strip

This owner extracts the exact rational identities from the symmetry-adapted
Apollonius discussion without promoting the Hilbert--Polya or RH claims.

The key sign convention is fixed here.  For

  w(s) = s / (s - 1),

one has formally

  d log w / ds = 1 / (s * (1 - s)),

so the inverse logarithmic scale factor is

  h(s) = s * (1 - s).

In centered coordinates z = s - 1/2 this is exactly

  h(z) = 1/4 - z^2.

The present file proves the algebraic coordinate identities and the Riccati
field realization.  It does not prove a global ODE flow, a self-adjoint
operator realization, or any statement that all zeta zeros lie on the
critical line.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge

open Complex
open InfoGeometry.Canonical.ComplexRiccatiSL2

/-- Centered coordinate around the functional-equation midpoint. -/
def centered (s : ℂ) : ℂ := s - (1 / 2 : ℂ)

/-- Recover the original Riemann coordinate from the centered coordinate. -/
def uncentered (z : ℂ) : ℂ := z + (1 / 2 : ℂ)

@[simp] theorem uncentered_centered (s : ℂ) :
    uncentered (centered s) = s := by
  simp [uncentered, centered]

@[simp] theorem centered_uncentered (z : ℂ) :
    centered (uncentered z) = z := by
  simp [uncentered, centered]

/-- The reflection involution becomes parity in centered coordinates. -/
theorem centered_reflection (s : ℂ) :
    centered (1 - s) = - centered s := by
  simp [centered]
  ring

/-- The reflection-ratio / Apollonius coordinate with foci 0 and 1. -/
def apolloniusRatio (s : ℂ) : ℂ :=
  s / (s - 1)

/-- Rational inverse of the Apollonius coordinate. -/
def invApolloniusRatio (w : ℂ) : ℂ :=
  w / (w - 1)

/-- Exact inverse on the affine chart away from the pole `s = 1`. -/
theorem invApolloniusRatio_apolloniusRatio
    (s : ℂ) (hs : s ≠ 1) :
    invApolloniusRatio (apolloniusRatio s) = s := by
  unfold invApolloniusRatio apolloniusRatio
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsm1]
  ring

/-- Reflection is multiplicative inversion in the ratio coordinate. -/
theorem apolloniusRatio_reflection
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    apolloniusRatio (1 - s) = (apolloniusRatio s)⁻¹ := by
  unfold apolloniusRatio
  have hs : s ≠ 0 := hs0
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hs, hsm1]
  ring

/-- The affine reflection has the unique fixed point `s = 1/2`. -/
theorem reflection_fixed_iff (s : ℂ) :
    1 - s = s ↔ s = (1 / 2 : ℂ) := by
  constructor
  · intro h
    have h' : s + s = 1 := by
      linear_combination -h
    calc
      s = (s + s) / 2 := by ring
      _ = 1 / 2 := by rw [h']
  · intro h
    subst s
    norm_num

/-- The exact inverse logarithmic transition factor in the original coordinate. -/
def logarithmicScale (s : ℂ) : ℂ :=
  s * (1 - s)

/-- In centered coordinates the scale factor is `1/4 - z^2`. -/
theorem logarithmicScale_centered (s : ℂ) :
    logarithmicScale s = (1 / 4 : ℂ) - centered s ^ 2 := by
  unfold logarithmicScale centered
  ring

/-- The same scale factor expressed directly in centered coordinates. -/
def centeredScale (z : ℂ) : ℂ :=
  (1 / 4 : ℂ) - z ^ 2

@[simp] theorem centeredScale_pos_half :
    centeredScale (1 / 2 : ℂ) = 0 := by
  norm_num [centeredScale]

@[simp] theorem centeredScale_neg_half :
    centeredScale (-1 / 2 : ℂ) = 0 := by
  norm_num [centeredScale]

/-- The only algebraic zeros of the centered scale factor are `±1/2`. -/
theorem centeredScale_eq_zero_iff (z : ℂ) :
    centeredScale z = 0 ↔ z = (1 / 2 : ℂ) ∨ z = (-1 / 2 : ℂ) := by
  unfold centeredScale
  constructor
  · intro h
    have hfac : ((1 / 2 : ℂ) - z) * ((1 / 2 : ℂ) + z) = 0 := by
      calc
        ((1 / 2 : ℂ) - z) * ((1 / 2 : ℂ) + z) = (1 / 4 : ℂ) - z ^ 2 := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · left
      exact (sub_eq_zero.mp hminus).symm
    · right
      field_simp at hplus ⊢
      linear_combination hplus
  · rintro (rfl | rfl) <;> norm_num

/-- The centered scale factor is literally an `sl2` Riccati vector field. -/
theorem centeredScale_eq_riccatiField (z : ℂ) :
    centeredScale z = riccatiField 0 (1 / 4 : ℂ) 1 z := by
  simp [centeredScale, riccatiField]

/-- The corresponding traceless `2 x 2` Riccati generator. -/
def apolloniusRiccatiGenerator : M2C :=
  riccatiMatrix 0 (1 / 4 : ℂ) 1

/-- Its determinant is the expected negative quarter. -/
theorem apolloniusRiccatiGenerator_det :
    Matrix.det apolloniusRiccatiGenerator = -(1 / 4 : ℂ) := by
  simp [apolloniusRiccatiGenerator, riccatiMatrix_det]

/-- The generator squares to one quarter of the identity. -/
theorem apolloniusRiccatiGenerator_sq :
    apolloniusRiccatiGenerator * apolloniusRiccatiGenerator =
      (1 / 4 : ℂ) • (1 : M2C) := by
  simpa [apolloniusRiccatiGenerator] using
    (riccatiMatrix_sq (0 : ℂ) (1 / 4 : ℂ) (1 : ℂ))

/-- Master finite packet for the corrected rational/Riccati coordinate layer. -/
theorem apollonius_riccati_packet (s z : ℂ) :
    centered (1 - s) = - centered s ∧
    logarithmicScale s = (1 / 4 : ℂ) - centered s ^ 2 ∧
    centeredScale z = riccatiField 0 (1 / 4 : ℂ) 1 z ∧
    (centeredScale z = 0 ↔ z = (1 / 2 : ℂ) ∨ z = (-1 / 2 : ℂ)) :=
  ⟨centered_reflection s,
    logarithmicScale_centered s,
    centeredScale_eq_riccatiField z,
    centeredScale_eq_zero_iff z⟩

end InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge

end noncomputable section
