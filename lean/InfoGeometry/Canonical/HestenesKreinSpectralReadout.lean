import InfoGeometry.Canonical.HestenesPhaseSpectral

/-!
# InfoGeometry.Canonical.HestenesKreinSpectralReadout

Concrete Hestenes/Krein matrix-coefficient readouts on the doubled real carrier.

This file avoids analytic spectral-theorem claims.  It proves the finite,
kernel-checkable part that is actually available from mathlib ancestry:
continuous linear operators have matrix coefficients, those coefficients are
linear in the operator argument, and they satisfy the standard Hilbert-space
operator norm bound.  The phase-axis theorem then reuses the existing
Hestenes-linearity eigenspace result.

#### BUCKET 1: CLOSED FINITE THEOREMS
* `matrixCoefficient_apply`
* `matrixCoefficient_add`
* `matrixCoefficient_neg`
* `matrixCoefficient_sub`
* `matrixCoefficient_smul`
* `norm_matrixCoefficient_le`
* `abs_matrixCoefficient_le`
* `hestenesKrein_spectralProjector_preserves_phaseAxis`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
* `hestenesKrein_spectralProjector_preserves_phaseAxis` depends on explicit
  Hestenes-linearity of the projector and an explicit eigenvector premise.

#### BUCKET 3: OPEN CLOSURE DEBT
* Construct spectral measures and reconstruction integrals elsewhere.
* Connect these concrete matrix coefficients to a full projection-valued
  spectral measure once the analytic corridor is closed.
-/

open scoped InnerProductSpace

namespace HestenesKreinSpectralReadout

open InfoGeometry.Canonical.HestenesPhaseSpectral
open InfoGeometry.Krein

universe u

section HestenesKrein

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Concrete real matrix coefficient of an operator on the doubled Hestenes/Krein
carrier.
-/
noncomputable def matrixCoefficient (A : EndH) (x y : H₂) : ℝ :=
  inner ℝ x (A y)

@[simp]
theorem matrixCoefficient_apply (A : EndH) (x y : H₂) :
    matrixCoefficient (E := E) A x y = inner ℝ x (A y) :=
  rfl

/-- Matrix coefficients are additive in the operator argument. -/
theorem matrixCoefficient_add (A B : EndH) (x y : H₂) :
    matrixCoefficient (E := E) (A + B) x y =
      matrixCoefficient (E := E) A x y + matrixCoefficient (E := E) B x y := by
  simp [matrixCoefficient, inner_add_right]

/-- Matrix coefficients commute with operator negation. -/
theorem matrixCoefficient_neg (A : EndH) (x y : H₂) :
    matrixCoefficient (E := E) (-A) x y = -matrixCoefficient (E := E) A x y := by
  simp [matrixCoefficient]

/-- Matrix coefficients are subtractive in the operator argument. -/
theorem matrixCoefficient_sub (A B : EndH) (x y : H₂) :
    matrixCoefficient (E := E) (A - B) x y =
      matrixCoefficient (E := E) A x y - matrixCoefficient (E := E) B x y := by
  simp [matrixCoefficient, inner_sub_right]

/-- Matrix coefficients are real-linear in the operator argument. -/
theorem matrixCoefficient_smul (c : ℝ) (A : EndH) (x y : H₂) :
    matrixCoefficient (E := E) (c • A) x y =
      c * matrixCoefficient (E := E) A x y := by
  simp [matrixCoefficient, real_inner_smul_right, mul_add]

/-- Hilbert-space operator norm bound for doubled-carrier matrix coefficients. -/
theorem norm_matrixCoefficient_le (A : EndH) (x y : H₂) :
    ‖matrixCoefficient (E := E) A x y‖ ≤ ‖x‖ * ‖A‖ * ‖y‖ := by
  calc
    ‖matrixCoefficient (E := E) A x y‖ = ‖inner ℝ x (A y)‖ := rfl
    _ ≤ ‖x‖ * ‖A y‖ := norm_inner_le_norm x (A y)
    _ ≤ ‖x‖ * (‖A‖ * ‖y‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm A y) (norm_nonneg x)
    _ = ‖x‖ * ‖A‖ * ‖y‖ := by ring

/-- Absolute-value form of the matrix-coefficient norm bound. -/
theorem abs_matrixCoefficient_le (A : EndH) (x y : H₂) :
    |matrixCoefficient (E := E) A x y| ≤ ‖x‖ * ‖A‖ * ‖y‖ := by
  simpa [Real.norm_eq_abs] using norm_matrixCoefficient_le (E := E) A x y

/--
Phase-axis compatibility for a projector with explicit Hestenes-linearity.

This is not a spectral-measure theorem.  It is the closed Hestenes/Krein
operator statement: an explicitly Hestenes-linear projector preserves the
phase-axis orbit of each real eigenspace.
-/
theorem hestenesKrein_spectralProjector_preserves_phaseAxis
    [CompleteSpace E]
    (P : EndH)
    (hP : IsHestenesLinear (E := E) P)
    (lam : ℝ)
    {v : H₂}
    (hv : IsEigenvector (E := E) P lam v) :
    IsEigenvector (E := E) P lam (clockAxis (E := E) v) :=
  eigenspace_phaseAxis_stable_of_hestenesLinear (E := E) P hP lam hv

end HestenesKrein

end HestenesKreinSpectralReadout
