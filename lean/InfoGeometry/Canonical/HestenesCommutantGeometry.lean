import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Clifford.Biquaternion
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.HestenesCommutantGeometry

Operator-coefficient Hestenes geometry in the commutant/normalizer of the
real doubled phase axis.

The primitive object is not scalar `i`; it is the real operator

`I = complex_i = Jε`

on the doubled Krein carrier.  Complexification of a coefficient algebra is
therefore represented by operator expressions of the form

* right convention: `A + B I`;
* left convention:  `A + I B`.

Theorems in this file are plain noncommutative endomorphism-algebra laws.
No witness packets, trace assumptions, diagonal models, or scalar-complex owner
language are introduced.
-/

namespace InfoGeometry.Canonical.HestenesCommutantGeometry

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.HestenesComplexTranslation

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Iₕ" => complex_i (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-! ## Commutant and normalizer predicates -/

/-- Coefficient operator commuting with the Hestenes phase axis. -/
@[rep_depth krein]
def CommutesWithHestenesK (A : EndH) : Prop :=
  A * Iₕ = Iₕ * A

/-- Coefficient operator anticommuting with the Hestenes phase axis. -/
@[rep_depth krein]
def AnticommutesWithHestenesK (A : EndH) : Prop :=
  A * Iₕ = -(Iₕ * A)

@[rep_depth krein]
theorem commutesWithHestenesK_iff_phaseLinear (A : EndH) :
    CommutesWithHestenesK (E := E) A ↔ IsPhaseLinear (E := E) A := by
  constructor
  · intro h
    unfold IsPhaseLinear
    apply ContinuousLinearMap.ext
    intro x
    simpa [InfoGeometry.Krein.clockAxis, ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndH => F x) h
  · intro h
    unfold CommutesWithHestenesK
    apply ContinuousLinearMap.ext
    intro x
    simpa [InfoGeometry.Krein.clockAxis, ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndH => F x) h

@[rep_depth krein]
theorem anticommutesWithHestenesK_iff_phaseAntilinear (A : EndH) :
    AnticommutesWithHestenesK (E := E) A ↔ IsPhaseAntilinear (E := E) A := by
  constructor
  · intro h
    unfold IsPhaseAntilinear
    apply ContinuousLinearMap.ext
    intro x
    simpa [AnticommutesWithHestenesK, InfoGeometry.Krein.clockAxis,
      ContinuousLinearMap.comp_apply] using congrArg (fun F : EndH => F x) h
  · intro h
    unfold AnticommutesWithHestenesK
    apply ContinuousLinearMap.ext
    intro x
    simpa [IsPhaseAntilinear, InfoGeometry.Krein.clockAxis,
      ContinuousLinearMap.comp_apply] using congrArg (fun F : EndH => F x) h

@[rep_depth krein]
theorem CommutesWithHestenesK.mul
    {A B : EndH}
    (hA : CommutesWithHestenesK (E := E) A)
    (hB : CommutesWithHestenesK (E := E) B) :
    CommutesWithHestenesK (E := E) (A * B) := by
  unfold CommutesWithHestenesK at hA hB ⊢
  calc
    A * B * Iₕ = A * (B * Iₕ) := by noncomm_ring
    _ = A * (Iₕ * B) := by rw [hB]
    _ = (A * Iₕ) * B := by noncomm_ring
    _ = (Iₕ * A) * B := by rw [hA]
    _ = Iₕ * (A * B) := by noncomm_ring

/-! ## Left-convention coefficient geometry `A + I B` -/

/-- Left-convention Hestenes coefficient expression `A + I B`. -/
@[rep_depth krein]
noncomputable def hestenesLeftCoeff (A B : EndH) : EndH :=
  A + Iₕ * B

@[simp, rep_depth krein]
theorem hestenesLeftCoeff_zero_zero :
    hestenesLeftCoeff (E := E) 0 0 = 0 := by
  simp [hestenesLeftCoeff]

@[simp, rep_depth krein]
theorem hestenesLeftCoeff_one_zero :
    hestenesLeftCoeff (E := E) (1 : EndH) 0 = 1 := by
  simp [hestenesLeftCoeff]

@[simp, rep_depth krein]
theorem hestenesLeftCoeff_zero_one :
    hestenesLeftCoeff (E := E) 0 (1 : EndH) = Iₕ := by
  simp [hestenesLeftCoeff]

/--
Left-convention noncommutative multiplication:

`(A + I B)(C + I D) = (AC - BD) + I(AD + BC)`.

The needed hypotheses are exactly that the left coefficients `A` and `B`
commute with the geometric imaginary.  No commutativity between coefficients is
assumed.
-/
@[rep_depth krein]
theorem hestenesLeftCoeff_mul
    (A B C D : EndH)
    (hA : CommutesWithHestenesK (E := E) A)
    (hB : CommutesWithHestenesK (E := E) B) :
    hestenesLeftCoeff (E := E) A B * hestenesLeftCoeff (E := E) C D =
      hestenesLeftCoeff (E := E) (A * C - B * D) (A * D + B * C) := by
  have hA' : A * Iₕ = Iₕ * A := hA
  have hB' : B * Iₕ = Iₕ * B := hB
  have hI2 : Iₕ * Iₕ = -(1 : EndH) := complex_i_sq (E := E)
  calc
    hestenesLeftCoeff (E := E) A B * hestenesLeftCoeff (E := E) C D
        = (A + Iₕ * B) * (C + Iₕ * D) := by
            rfl
    _ = A * C + A * (Iₕ * D) + (Iₕ * B) * C + (Iₕ * B) * (Iₕ * D) := by
          noncomm_ring
    _ = A * C + Iₕ * (A * D) + Iₕ * (B * C) - B * D := by
          have hAID : A * (Iₕ * D) = Iₕ * (A * D) := by
            calc
              A * (Iₕ * D) = (A * Iₕ) * D := by noncomm_ring
              _ = (Iₕ * A) * D := by rw [hA']
              _ = Iₕ * (A * D) := by noncomm_ring
          have hIBID : (Iₕ * B) * (Iₕ * D) = -B * D := by
            calc
              (Iₕ * B) * (Iₕ * D) = Iₕ * B * Iₕ * D := by noncomm_ring
              _ = Iₕ * (B * Iₕ) * D := by noncomm_ring
              _ = Iₕ * (Iₕ * B) * D := by rw [hB']
              _ = (Iₕ * Iₕ) * B * D := by noncomm_ring
              _ = (-(1 : EndH)) * B * D := by rw [hI2]
              _ = -B * D := by simp
          rw [hAID, hIBID]
          noncomm_ring
    _ = (A * C - B * D) + Iₕ * (A * D + B * C) := by
          noncomm_ring
    _ = hestenesLeftCoeff (E := E) (A * C - B * D) (A * D + B * C) := by
          rfl

/--
The left and right coefficient conventions agree when the second coefficient
commutes with the Hestenes axis.
-/
@[rep_depth krein]
theorem hestenesLeftCoeff_eq_hestenesCoeff_of_commutes
    (A B : EndH)
    (hB : CommutesWithHestenesK (E := E) B) :
    hestenesLeftCoeff (E := E) A B =
      _root_.InfoGeometry.Canonical.HestenesComplexTranslation.hestenesCoeff (E := E) A B := by
  have hB' : B * Iₕ = Iₕ * B := hB
  simp [hestenesLeftCoeff, _root_.InfoGeometry.Canonical.HestenesComplexTranslation.hestenesCoeff,
    hB'.symm]

/-! ## Normalizer transport laws -/

/-- A two-sided frame change preserves the Hestenes phase axis by conjugation. -/
@[rep_depth krein]
def PreservesHestenesK (U V : EndH) : Prop :=
  V * U = 1 ∧ U * V = 1 ∧ U * Iₕ * V = Iₕ

/-- A two-sided frame change flips the Hestenes phase axis by conjugation. -/
@[rep_depth krein]
def FlipsHestenesK (U V : EndH) : Prop :=
  V * U = 1 ∧ U * V = 1 ∧ U * Iₕ * V = -Iₕ

/--
Phase-preserving normalizer transport of left-convention Hestenes coefficients.
-/
@[rep_depth krein]
theorem conjugate_hestenesLeftCoeff_of_preservesK
    (U V A B A' B' : EndH)
    (hK : PreservesHestenesK (E := E) U V)
    (hA : U * A * V = A')
    (hB : U * B * V = B') :
    U * hestenesLeftCoeff (E := E) A B * V =
      hestenesLeftCoeff (E := E) A' B' := by
  rcases hK with ⟨hVU, hUV, hUIV⟩
  have hConjB : U * (Iₕ * B) * V = (U * Iₕ * V) * (U * B * V) := by
    calc
      U * (Iₕ * B) * V = U * Iₕ * B * V := by noncomm_ring
      _ = U * Iₕ * (1 : EndH) * B * V := by simp
      _ = U * Iₕ * (V * U) * B * V := by rw [hVU]
      _ = (U * Iₕ * V) * (U * B * V) := by noncomm_ring
  calc
    U * hestenesLeftCoeff (E := E) A B * V
        = U * (A + Iₕ * B) * V := by
            rfl
    _ = U * A * V + U * (Iₕ * B) * V := by
          noncomm_ring
    _ = A' + (U * Iₕ * V) * (U * B * V) := by
          rw [hA, hConjB]
    _ = A' + Iₕ * B' := by
          rw [hUIV, hB]
    _ = hestenesLeftCoeff (E := E) A' B' := by
          rfl

/--
Phase-flipping normalizer transport implements conjugation of the Hestenes
coefficient axis.
-/
@[rep_depth krein]
theorem conjugate_hestenesLeftCoeff_of_flipsK
    (U V A B A' B' : EndH)
    (hK : FlipsHestenesK (E := E) U V)
    (hA : U * A * V = A')
    (hB : U * B * V = B') :
    U * hestenesLeftCoeff (E := E) A B * V =
      hestenesLeftCoeff (E := E) A' (-B') := by
  rcases hK with ⟨hVU, hUV, hUIV⟩
  have hConjB : U * (Iₕ * B) * V = (U * Iₕ * V) * (U * B * V) := by
    calc
      U * (Iₕ * B) * V = U * Iₕ * B * V := by noncomm_ring
      _ = U * Iₕ * (1 : EndH) * B * V := by simp
      _ = U * Iₕ * (V * U) * B * V := by rw [hVU]
      _ = (U * Iₕ * V) * (U * B * V) := by noncomm_ring
  calc
    U * hestenesLeftCoeff (E := E) A B * V
        = U * (A + Iₕ * B) * V := by
            rfl
    _ = U * A * V + U * (Iₕ * B) * V := by
          noncomm_ring
    _ = A' + (U * Iₕ * V) * (U * B * V) := by
          rw [hA, hConjB]
    _ = A' + (-Iₕ) * B' := by
          rw [hUIV, hB]
    _ = A' + Iₕ * (-B') := by
          noncomm_ring
    _ = hestenesLeftCoeff (E := E) A' (-B') := by
          rfl

end Core

end InfoGeometry.Canonical.HestenesCommutantGeometry
