import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.NoncommutativeModularSignum
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.HestenesComplexTranslation

Canonical real-doubled Hestenes translation of complex scalar and
operator-coefficient language.

The owner axis is the concrete doubled-space operator

`K = complex_i = Jε`.

This file adds the theorem-level spine:

* `a+bi ↦ a·1 + b·K` as an endomorphism-level scalar embedding;
* `A+B·K` as the operator-coefficient Hestenes object;
* multiplication law using `K² = -1`;
* complex conjugation as real-linear modular reflection by `J`;
* complex-linearity as commuting with the Hestenes phase axis;
* positive boost signum as the sign of the real Hestenes boost sector.

No new property packets are introduced.
-/

namespace InfoGeometry.Canonical.HestenesComplexTranslation

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.NoncommutativeModularSignum

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Iₕ" => complex_i (E := E)
local notation "J" => modular_j (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Hestenes scalar embedding `a+bi ↦ a·1 + b·K`. -/
@[rep_depth krein]
noncomputable def hestenesScalar (z : ℂ) : EndH :=
  z.re • (1 : EndH) + z.im • Iₕ

@[simp, rep_depth krein]
theorem hestenesScalar_zero :
    hestenesScalar (E := E) 0 = 0 := by
  simp [hestenesScalar]

@[simp, rep_depth krein]
theorem hestenesScalar_one :
    hestenesScalar (E := E) 1 = (1 : EndH) := by
  simp [hestenesScalar]

@[simp, rep_depth krein]
theorem hestenesScalar_I :
    hestenesScalar (E := E) Complex.I = Iₕ := by
  simp [hestenesScalar]

/-- The embedded imaginary unit squares to `-1`. -/
@[rep_depth krein]
theorem hestenesScalar_I_sq :
    hestenesScalar (E := E) Complex.I * hestenesScalar (E := E) Complex.I =
      -(1 : EndH) := by
  simpa [hestenesScalar_I] using complex_i_sq (E := E)

/-! ## Operator-coefficient Hestenes algebra -/

/--
Operator-coefficient Hestenes element `A + B I`.

This is the noncommutative owner object.  Scalar `a+bi` is only the special
case `A = a·1`, `B = b·1`.
-/
@[rep_depth krein]
noncomputable def hestenesCoeff (A B : EndH) : EndH :=
  A + B * Iₕ

@[simp, rep_depth krein]
theorem hestenesCoeff_zero_zero :
    hestenesCoeff (E := E) 0 0 = 0 := by
  simp [hestenesCoeff]

@[simp, rep_depth krein]
theorem hestenesCoeff_one_zero :
    hestenesCoeff (E := E) (1 : EndH) 0 = 1 := by
  simp [hestenesCoeff]

@[simp, rep_depth krein]
theorem hestenesCoeff_zero_one :
    hestenesCoeff (E := E) 0 (1 : EndH) = Iₕ := by
  simp [hestenesCoeff]

/--
The operator-coefficient imaginary unit squares to `-1`.
-/
@[rep_depth krein]
theorem hestenesCoeff_I_sq :
    hestenesCoeff (E := E) 0 (1 : EndH) *
      hestenesCoeff (E := E) 0 (1 : EndH) = -(1 : EndH) := by
  simpa [hestenesCoeff_zero_one] using complex_i_sq (E := E)

/--
Scalar Hestenes embedding is the operator-coefficient construction with
central real coefficients.
-/
@[rep_depth krein]
theorem hestenesScalar_eq_hestenesCoeff_real_coeff (z : ℂ) :
    hestenesScalar (E := E) z =
      hestenesCoeff (E := E) (z.re • (1 : EndH)) (z.im • (1 : EndH)) := by
  simp [hestenesScalar, hestenesCoeff, mul_assoc]

/--
Noncommutative operator-coefficient multiplication.

Only the right factor coefficients must commute with the Hestenes axis for
the usual ordered formula to hold:

`(A + B I)(C + D I) = (AC - BD) + (AD + BC)I`.

No commutativity of the coefficient algebra is assumed.
-/
@[rep_depth krein]
theorem hestenesCoeff_mul
    (A B C D : EndH)
    (hC : Iₕ * C = C * Iₕ)
    (hD : Iₕ * D = D * Iₕ) :
    hestenesCoeff (E := E) A B * hestenesCoeff (E := E) C D =
      hestenesCoeff (E := E) (A * C - B * D) (A * D + B * C) := by
  have hI2 : Iₕ * Iₕ = -(1 : EndH) := complex_i_sq (E := E)
  calc
    hestenesCoeff (E := E) A B * hestenesCoeff (E := E) C D
        = (A + B * Iₕ) * (C + D * Iₕ) := by
            rfl
    _ = A * C + A * (D * Iₕ) + (B * Iₕ) * C + (B * Iₕ) * (D * Iₕ) := by
          noncomm_ring
    _ = A * C + A * D * Iₕ + B * C * Iₕ + B * D * (Iₕ * Iₕ) := by
          have hBC : (B * Iₕ) * C = B * C * Iₕ := by
            calc
              (B * Iₕ) * C = B * (Iₕ * C) := by noncomm_ring
              _ = B * (C * Iₕ) := by rw [hC]
              _ = B * C * Iₕ := by noncomm_ring
          have hBD : (B * Iₕ) * (D * Iₕ) = B * D * (Iₕ * Iₕ) := by
            calc
              (B * Iₕ) * (D * Iₕ) = B * (Iₕ * D) * Iₕ := by noncomm_ring
              _ = B * (D * Iₕ) * Iₕ := by rw [hD]
              _ = B * D * (Iₕ * Iₕ) := by noncomm_ring
          rw [← mul_assoc A D Iₕ, hBC, hBD]
    _ = A * C + A * D * Iₕ + B * C * Iₕ - B * D := by
          rw [hI2]
          noncomm_ring
    _ = (A * C - B * D) + (A * D + B * C) * Iₕ := by
          noncomm_ring
    _ = hestenesCoeff (E := E) (A * C - B * D) (A * D + B * C) := by
          rfl

/--
If both coefficients commute with the Hestenes axis, then the
operator-coefficient element also commutes with the axis.
-/
@[rep_depth krein]
theorem hestenesCoeff_isPhaseLinear
    (A B : EndH)
    (hA : A * Iₕ = Iₕ * A)
    (hB : B * Iₕ = Iₕ * B) :
    IsPhaseLinear (E := E) (hestenesCoeff (E := E) A B) := by
  unfold IsPhaseLinear hestenesCoeff
  have hI2 : Iₕ * Iₕ = -(1 : EndH) := complex_i_sq (E := E)
  calc
    (A + B * Iₕ) * Iₕ
        = A * Iₕ + B * (Iₕ * Iₕ) := by noncomm_ring
    _ = Iₕ * A + B * (Iₕ * Iₕ) := by rw [hA]
    _ = Iₕ * A - B := by
          rw [hI2]
          noncomm_ring
    _ = Iₕ * (A + B * Iₕ) := by
          have hIBI : Iₕ * (B * Iₕ) = -B := by
            calc
              Iₕ * (B * Iₕ) = (Iₕ * B) * Iₕ := by noncomm_ring
              _ = (B * Iₕ) * Iₕ := by rw [← hB]
              _ = B * (Iₕ * Iₕ) := by noncomm_ring
              _ = B * (-(1 : EndH)) := by rw [hI2]
              _ = -B := by simp
          rw [mul_add, hIBI]
          abel

/--
Modular reflection conjugates a `J`-fixed operator-coefficient Hestenes
element by flipping the Hestenes imaginary axis.

This is the real operator form of complex conjugation:
`J(A+B I)J = A-BI` when `A` and `B` are fixed by `J`.
-/
@[rep_depth krein]
theorem modular_j_conjugates_hestenesCoeff_of_fixed
    (A B : EndH)
    (hA : J * A * J = A)
    (hB : J * B * J = B) :
    J * hestenesCoeff (E := E) A B * J =
      hestenesCoeff (E := E) A (-B) := by
  have hJ2 : J * J = (1 : EndH) := modular_j_involution (E := E)
  have hJIJ : J * Iₕ * J = -Iₕ := by
    calc
      J * Iₕ * J = J * (Iₕ * J) := by rw [mul_assoc]
      _ = J * (-spectral_epsilon (E := E)) := by
            rw [show Iₕ * J = -spectral_epsilon (E := E) by
              simpa using complex_i_comp_modular_j (E := E)]
      _ = -(J * spectral_epsilon (E := E)) := by simp
      _ = -Iₕ := by rfl
  have hConjMul : J * (B * Iₕ) * J = (J * B * J) * (J * Iₕ * J) := by
    calc
      J * (B * Iₕ) * J = J * B * Iₕ * J := by noncomm_ring
      _ = J * B * (1 : EndH) * Iₕ * J := by simp
      _ = J * B * (J * J) * Iₕ * J := by rw [hJ2]
      _ = (J * B * J) * (J * Iₕ * J) := by noncomm_ring
  calc
    J * hestenesCoeff (E := E) A B * J
        = J * (A + B * Iₕ) * J := by
            rfl
    _ = J * A * J + J * (B * Iₕ) * J := by
          noncomm_ring
    _ = A + (J * B * J) * (J * Iₕ * J) := by
          rw [hA]
          rw [hConjMul]
    _ = A + B * (-Iₕ) := by
          rw [hB, hJIJ]
    _ = A + (-B) * Iₕ := by
          noncomm_ring
    _ = hestenesCoeff (E := E) A (-B) := by
          rfl

/-- Scalar embedding acts on vectors exactly as the existing `RealBdG.complexAction`. -/
@[rep_depth krein]
theorem hestenesScalar_apply_eq_complexAction (z : ℂ) (v : H₂) :
    hestenesScalar (E := E) z v =
      InfoGeometry.Canonical.RealBdG.complexAction (E := E) z v := by
  simp [hestenesScalar, InfoGeometry.Canonical.RealBdG.complexAction,
    InfoGeometry.Canonical.RealBdG.modularK_eq_complex_i]

/-- Commuting with all Hestenes scalars implies phase-linearity. -/
@[rep_depth krein]
theorem isPhaseLinear_of_commutes_hestenesScalar
    (A : EndH)
    (h : ∀ z : ℂ, A * hestenesScalar (E := E) z =
      hestenesScalar (E := E) z * A) :
    IsPhaseLinear (E := E) A := by
  have hI := h Complex.I
  simpa [IsPhaseLinear, hestenesScalar_I, InfoGeometry.Krein.clockAxis] using hI

/-- Phase-linear operators commute with every Hestenes scalar. -/
@[rep_depth krein]
theorem commutes_hestenesScalar_of_isPhaseLinear
    (A : EndH)
    (hA : IsPhaseLinear (E := E) A) :
    ∀ z : ℂ, A * hestenesScalar (E := E) z =
      hestenesScalar (E := E) z * A := by
  intro z
  have hK : A * Iₕ = Iₕ * A := by
    simpa [IsPhaseLinear, InfoGeometry.Krein.clockAxis] using hA
  apply ContinuousLinearMap.ext
  intro x
  have hKx : A (Iₕ x) = Iₕ (A x) := by
    simpa using congrArg (fun F : EndH => F x) hK
  calc
    (A * hestenesScalar (E := E) z) x
        = z.re • A x + z.im • A (Iₕ x) := by
            simp [hestenesScalar]
    _ = z.re • A x + z.im • Iₕ (A x) := by rw [hKx]
    _ = (hestenesScalar (E := E) z * A) x := by
            simp [hestenesScalar]

/-- Complex-linearity readback: commute with all embedded scalars iff commute with `K`. -/
@[rep_depth krein]
theorem hestenesScalar_commutes_iff_phaseLinear (A : EndH) :
    (∀ z : ℂ, A * hestenesScalar (E := E) z =
      hestenesScalar (E := E) z * A)
      ↔ IsPhaseLinear (E := E) A := by
  constructor
  · exact isPhaseLinear_of_commutes_hestenesScalar (E := E) A
  · exact commutes_hestenesScalar_of_isPhaseLinear (E := E) A

/-- Modular reflection conjugates the Hestenes imaginary axis to its negative. -/
@[rep_depth krein]
theorem modular_j_conjugates_complex_i :
    J * Iₕ * J = -Iₕ := by
  calc
    J * Iₕ * J = J * (Iₕ * J) := by rw [mul_assoc]
    _ = J * (-spectral_epsilon (E := E)) := by
          rw [show Iₕ * J = -spectral_epsilon (E := E) by
            simpa using complex_i_comp_modular_j (E := E)]
    _ = -(J * spectral_epsilon (E := E)) := by simp
    _ = -Iₕ := by rfl

/-- Modular reflection implements complex conjugation on embedded Hestenes scalars. -/
@[rep_depth krein]
theorem modular_j_conjugates_hestenesScalar (z : ℂ) :
    J * hestenesScalar (E := E) z * J =
      hestenesScalar (E := E) (star z) := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [hestenesScalar, modular_j, complex_i]

/-- Positive Hestenes boost signum is exactly the doubled sign operator `ε`. -/
@[rep_depth krein]
theorem hestenesBoostSignum_eq_epsilon_of_pos {t : ℝ} (ht : 0 < t) :
    doubledBoostSignum (E := E) t = spectral_epsilon (E := E) :=
  doubledBoostSignum_of_pos (E := E) ht

/-- Positive Hestenes boost signum squares to identity. -/
@[rep_depth krein]
theorem hestenesBoostSignum_sq_of_pos {t : ℝ} (ht : 0 < t) :
    doubledBoostSignum (E := E) t * doubledBoostSignum (E := E) t = (1 : EndH) :=
  doubledBoostSignum_sq_of_ne_zero (E := E) (ne_of_gt ht)

end Core

end InfoGeometry.Canonical.HestenesComplexTranslation
