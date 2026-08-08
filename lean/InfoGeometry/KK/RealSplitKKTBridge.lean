import InfoGeometry.Canonical.KKTCore
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.RealSplitKKTBridge

KKT-grade bridge for the primitive bounded real split-Krein Fredholm carrier.

This bridge is intentionally explicit about the only extra property it needs:
the ambient `Γ`-grading on the Krein module agrees with the split-`Cl(1,1)`
pseudoscalar `eps` carried by the cycle.

Under that property:

- even algebra representations land in KKT grade zero,
- the odd phase has zero KKT grade-zero component,
- the odd phase splits exactly into the `g₁ ⊕ g₋₁` channels.
-/


namespace InfoGeometry.KK.RealSplitKKTBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Krein
open InfoGeometry.Krein.KreinGradedModule
open InfoGeometry.KK

section Core

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

local notation "EndH" => H →L[ℝ] H


@[rep_depth krein] theorem pi_isGZero_of_gradeCLM_eq_eps
    (X : RealSplitKreinKasparovCycle A B H)
    (hGrade : gradeCLM (H := H) = X.cl11.eps)
    (a : A) :
    IsGZero X.cl11 (X.π a) := by
  have hEven : IsEven (H := H) (X.π a) := X.π_even_apply a
  have hConj : epsConj X.cl11 (X.π a) = X.π a := by
    unfold IsEven gradeConj at hEven
    simpa [epsConj, hGrade, mul_assoc] using hEven
  exact isGZero_of_epsConj_eq (X := X.cl11) hConj

@[rep_depth krein] theorem rho_isGZero_of_gradeCLM_eq_eps
    (X : RealSplitKreinKasparovCycle A B H)
    (hGrade : gradeCLM (H := H) = X.cl11.eps)
    (b : B) :
    IsGZero X.cl11 (X.ρ b) := by
  have hEven : IsEven (H := H) (X.ρ b) := X.ρ_even_apply b
  have hConj : epsConj X.cl11 (X.ρ b) = X.ρ b := by
    unfold IsEven gradeConj at hEven
    simpa [epsConj, hGrade, mul_assoc] using hEven
  exact isGZero_of_epsConj_eq (X := X.cl11) hConj

@[rep_depth krein] theorem gZeroPart_F_eq_zero_of_gradeCLM_eq_eps
    (X : RealSplitKreinKasparovCycle A B H)
    (hGrade : gradeCLM (H := H) = X.cl11.eps) :
    gZeroPart X.cl11 X.F = 0 := by
  have hOdd : IsOdd (H := H) X.F := X.F_odd
  have hConj : epsConj X.cl11 X.F = -X.F := by
    unfold IsOdd gradeConj at hOdd
    simpa [epsConj, hGrade, mul_assoc] using hOdd
  exact gZeroPart_eq_zero_of_epsConj_neg (X := X.cl11) hConj

@[rep_depth krein] theorem F_eq_gOnePart_add_gNegOnePart_of_gradeCLM_eq_eps
    (X : RealSplitKreinKasparovCycle A B H)
    (hGrade : gradeCLM (H := H) = X.cl11.eps) :
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F := by
  have hOdd : IsOdd (H := H) X.F := X.F_odd
  have hConj : epsConj X.cl11 X.F = -X.F := by
    unfold IsOdd gradeConj at hOdd
    simpa [epsConj, hGrade, mul_assoc] using hOdd
  exact gOnePart_add_gNegOnePart_eq_of_epsConj_neg (X := X.cl11) hConj


end Core

end InfoGeometry.KK.RealSplitKKTBridge
