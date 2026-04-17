import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.Cl11PolarizedBasis

Circularly polarized `u⁺/u⁻` operator basis for the real split `Cl(1,1)` lane.

This file does **not** claim the full Lorentz/modular orbit theorem.
It only installs the exact polarized operator channels already implicit in
`KKTCore`:

- `uPlus  := gOnePart`
- `uMinus := gNegOnePart`

and proves the first structural laws needed later for Cartan/Lorentz action:

- odd grading with respect to `eps`,
- nilpotent square-zero laws,
- mixed products land in the grade-zero sector.

So this file is a lawful basis/translator layer rather than a capstone.
-/

namespace InfoGeometry.Canonical.Cl11PolarizedBasis

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Quantum

section Core

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

/-- Circularly polarized `u⁺` channel: the grade `+1` off-diagonal part. -/
@[rep_depth krein]
noncomputable def uPlus (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  gOnePart X A

/-- Circularly polarized `u⁻` channel: the grade `-1` off-diagonal part. -/
@[rep_depth krein]
noncomputable def uMinus (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  gNegOnePart X A

/-- Exact `u⁺ = g₁` identification. -/
@[simp, rep_depth krein] theorem uPlus_eq_gOnePart
    (X : RealSplitCl11Action H) (A : EndH) :
    uPlus X A = gOnePart X A := rfl

/-- Exact `u⁻ = g₋₁` identification. -/
@[simp, rep_depth krein] theorem uMinus_eq_gNegOnePart
    (X : RealSplitCl11Action H) (A : EndH) :
    uMinus X A = gNegOnePart X A := rfl

/-- `u⁺` is linear in its operator argument. -/
@[simp, rep_depth krein] theorem uPlus_add
    (X : RealSplitCl11Action H) (A B : EndH) :
    uPlus X (A + B) = uPlus X A + uPlus X B := by
  simp [uPlus]

/-- `u⁺` is homogeneous in its operator argument. -/
@[simp, rep_depth krein] theorem uPlus_smul
    (X : RealSplitCl11Action H) (r : ℝ) (A : EndH) :
    uPlus X (r • A) = r • uPlus X A := by
  simp [uPlus]

/-- `u⁻` is linear in its operator argument. -/
@[simp, rep_depth krein] theorem uMinus_add
    (X : RealSplitCl11Action H) (A B : EndH) :
    uMinus X (A + B) = uMinus X A + uMinus X B := by
  simp [uMinus]

/-- `u⁻` is homogeneous in its operator argument. -/
@[simp, rep_depth krein] theorem uMinus_smul
    (X : RealSplitCl11Action H) (r : ℝ) (A : EndH) :
    uMinus X (r • A) = r • uMinus X A := by
  simp [uMinus]

/-- `u⁺` is exactly grade `+1`. -/
@[rep_depth krein] theorem isGOne_uPlus
    (X : RealSplitCl11Action H) (A : EndH) :
    IsGOne X (uPlus X A) := by
  unfold IsGOne uPlus gOnePart
  calc
    plusProjector X * (plusProjector X * A * minusProjector X) * minusProjector X
        = (plusProjector X * plusProjector X) * A * (minusProjector X * minusProjector X) := by
            simp [mul_assoc]
    _ = plusProjector X * A * minusProjector X := by
          rw [plusProjector_idempotent, minusProjector_idempotent]

/-- `u⁻` is exactly grade `-1`. -/
@[rep_depth krein] theorem isGNegOne_uMinus
    (X : RealSplitCl11Action H) (A : EndH) :
    IsGNegOne X (uMinus X A) := by
  unfold IsGNegOne uMinus gNegOnePart
  calc
    minusProjector X * (minusProjector X * A * plusProjector X) * plusProjector X
        = (minusProjector X * minusProjector X) * A * (plusProjector X * plusProjector X) := by
            simp [mul_assoc]
    _ = minusProjector X * A * plusProjector X := by
          rw [minusProjector_idempotent, plusProjector_idempotent]

/-- `u⁺` anticommutes with the Clifford grading involution `eps`. -/
@[rep_depth krein] theorem eps_mul_eq_neg_mul_eps_of_isUPlus
    (X : RealSplitCl11Action H) {A : EndH} :
    X.eps * uPlus X A = -(uPlus X A * X.eps) := by
  exact eps_mul_eq_neg_mul_eps_of_isGOne (X := X) (A := uPlus X A)
    (isGOne_uPlus (X := X) (A := A))

/-- `u⁻` anticommutes with the Clifford grading involution `eps`. -/
@[rep_depth krein] theorem eps_mul_eq_neg_mul_eps_of_isUMinus
    (X : RealSplitCl11Action H) {A : EndH} :
    X.eps * uMinus X A = -(uMinus X A * X.eps) := by
  exact eps_mul_eq_neg_mul_eps_of_isGNegOne (X := X) (A := uMinus X A)
    (isGNegOne_uMinus (X := X) (A := A))

/-- Nilpotent square-zero law for the circularly polarized `u⁺` channel. -/
@[rep_depth krein] theorem uPlus_mul_uPlus_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    uPlus X A * uPlus X B = 0 := by
  simpa [uPlus] using gOnePart_mul_gOnePart_eq_zero (X := X) A B

/-- Nilpotent square-zero law for the circularly polarized `u⁻` channel. -/
@[rep_depth krein] theorem uMinus_mul_uMinus_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    uMinus X A * uMinus X B = 0 := by
  simpa [uMinus] using gNegOnePart_mul_gNegOnePart_eq_zero (X := X) A B

/-- Mixed `u⁺u⁻` products land in the grade-zero sector. -/
@[rep_depth krein] theorem uPlus_mul_uMinus_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (uPlus X A * uMinus X B) := by
  simpa [uPlus, uMinus] using gOnePart_mul_gNegOnePart_isGZero (X := X) A B

/-- Mixed `u⁻u⁺` products land in the grade-zero sector. -/
@[rep_depth krein] theorem uMinus_mul_uPlus_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (uMinus X A * uPlus X B) := by
  simpa [uPlus, uMinus] using gNegOnePart_mul_gOnePart_isGZero (X := X) A B

/-- The commutator of `u⁺` and `u⁻` lands in the grade-zero sector. -/
@[rep_depth krein] theorem commutator_uPlus_uMinus_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (commutator (uPlus X A) (uMinus X B)) := by
  simpa [uPlus, uMinus] using
    commutator_gOne_gNegOne_isGZero (X := X) A B

end Core

section DoubledSpaceSpecialization

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Canonical doubled-space `u⁺` channel. -/
@[rep_depth krein]
noncomputable def doubledUPlus (A : EndH) : EndH :=
  uPlus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A

/-- Canonical doubled-space `u⁻` channel. -/
@[rep_depth krein]
noncomputable def doubledUMinus (A : EndH) : EndH :=
  uMinus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A

@[simp, rep_depth krein] theorem doubledUPlus_mul_doubledUPlus_eq_zero
    (A B : EndH) :
    doubledUPlus (E := E) A * doubledUPlus (E := E) B = 0 := by
  change uPlus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A *
      uPlus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) B = 0
  exact uPlus_mul_uPlus_eq_zero
    (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A B

@[simp, rep_depth krein] theorem doubledUMinus_mul_doubledUMinus_eq_zero
    (A B : EndH) :
    doubledUMinus (E := E) A * doubledUMinus (E := E) B = 0 := by
  change uMinus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A *
      uMinus (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) B = 0
  exact uMinus_mul_uMinus_eq_zero
    (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A B

@[rep_depth krein] theorem doubled_commutator_uPlus_uMinus_isGZero
    (A B : EndH) :
    IsGZero (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E))
      (commutator (doubledUPlus (E := E) A) (doubledUMinus (E := E) B)) := by
  simpa [doubledUPlus, doubledUMinus] using
    commutator_uPlus_uMinus_isGZero
      (X := InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)) A B

end DoubledSpaceSpecialization

end InfoGeometry.Canonical.Cl11PolarizedBasis
