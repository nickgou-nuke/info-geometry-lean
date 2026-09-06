import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge

/-!
# The actual entire xi logarithmic differential on its zero-free domain

This owner packages the already-defined global logarithmic readout on the
actual zero-free locus of the completed Riemann xi function.  The subtype
records the domain restriction, and the reflection theorem transports the
existing pullback identity to that domain.  No de Rham class, contour period,
or zero multiplicity theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus

abbrev EntireXiZeroFreePoint :=
  {s : ℂ // s ∈ entireRiemannXiZeroFreeLocus}

def entireRiemannXiLogOneFormOnZeroFree
    (s : EntireXiZeroFreePoint) : ℂ →L[ℂ] ℂ :=
  entireRiemannXiLogOneForm s.1

def reflectZeroFree (s : EntireXiZeroFreePoint) : EntireXiZeroFreePoint :=
  ⟨1 - s.1, entireRiemannXiZeroFree_reflection s.property⟩

def conjugateZeroFree (s : EntireXiZeroFreePoint) : EntireXiZeroFreePoint :=
  ⟨star s.1, (entireRiemannXiZeroFree_conjugation_iff s.1).2 s.property⟩

@[simp] theorem reflectZeroFree_involutive
    (s : EntireXiZeroFreePoint) :
    reflectZeroFree (reflectZeroFree s) = s := by
  apply Subtype.ext
  simp [reflectZeroFree]

@[simp] theorem conjugateZeroFree_involutive
    (s : EntireXiZeroFreePoint) :
    conjugateZeroFree (conjugateZeroFree s) = s := by
  apply Subtype.ext
  simp [conjugateZeroFree]

theorem reflectZeroFree_conjugate_commute
    (s : EntireXiZeroFreePoint) :
    reflectZeroFree (conjugateZeroFree s) =
      conjugateZeroFree (reflectZeroFree s) := by
  apply Subtype.ext
  simp [reflectZeroFree, conjugateZeroFree]

@[simp] theorem entireRiemannXiLogOneFormOnZeroFree_apply
    (s : EntireXiZeroFreePoint) (v : ℂ) :
    entireRiemannXiLogOneFormOnZeroFree s v =
      v * entireRiemannXiLogDifferential s.1 := by
  simp [entireRiemannXiLogOneFormOnZeroFree]

theorem entireRiemannXiLogOneFormOnZeroFree_reflection_pullback
    (s : EntireXiZeroFreePoint) (v : ℂ) :
    entireRiemannXiLogOneFormOnZeroFree (reflectZeroFree s) (-v) =
      entireRiemannXiLogOneFormOnZeroFree s v := by
  exact entireRiemannXiLogOneForm_reflection_pullback s.1 v

theorem entireRiemannXi_mul_logDifferential_on_zeroFree
    (s : EntireXiZeroFreePoint) :
    entireRiemannXi s.1 * entireRiemannXiLogDifferential s.1 =
      -deriv entireRiemannXi s.1 := by
  rw [entireRiemannXiLogDifferential_eq]
  have hcancel :
      entireRiemannXi s.1 *
          (deriv entireRiemannXi s.1 / entireRiemannXi s.1) =
        deriv entireRiemannXi s.1 := by
    rw [div_eq_mul_inv]
    calc
      entireRiemannXi s.1 *
            (deriv entireRiemannXi s.1 * (entireRiemannXi s.1)⁻¹) =
          deriv entireRiemannXi s.1 *
            (entireRiemannXi s.1 * (entireRiemannXi s.1)⁻¹) := by ring
      _ = deriv entireRiemannXi s.1 := by
        rw [mul_inv_cancel₀ s.property, mul_one]
  rw [mul_neg, hcancel]

theorem entireRiemannXiLogDifferential_on_zeroFree_eq_regular
    (s : EntireXiZeroFreePoint) (hs0 : s.1 ≠ 0) (hs1 : s.1 ≠ 1) :
    entireRiemannXiLogDifferential s.1 =
      actualRiemannXiLogDifferential s.1 := by
  exact entireRiemannXiLogDifferential_eq_actualRiemannXiLogDifferential hs0 hs1

theorem entireRiemannXiLogOneFormOnZeroFree_eq_regular
    (s : EntireXiZeroFreePoint) (hs0 : s.1 ≠ 0) (hs1 : s.1 ≠ 1) :
    entireRiemannXiLogOneFormOnZeroFree s =
      actualRiemannXiLogOneForm s.1 := by
  simpa [entireRiemannXiLogOneFormOnZeroFree] using
    (entireRiemannXiLogOneForm_eq_actualRiemannXiLogOneForm hs0 hs1)

end InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential
