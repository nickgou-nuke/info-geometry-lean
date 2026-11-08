import InfoGeometry.Canonical.RestrictedVolumeCharacter
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.CartanBerezinianCore

open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Krein
open InfoGeometry.Volume.Base

section Schur

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Admissible doubled transport carrying the data needed for a Schur-complement Berezinian. -/
structure SchurAdmissibleTransport where
  T : DoubledSpace E →L[ℝ] DoubledSpace E
  Dinv : E ≃L[ℝ] E
  hD : minusBlockMap (E := E) T = (Dinv : E →L[ℝ] E)
  Schur : E ≃L[ℝ] E
  hSchur :
    plusBlockMap (E := E) T
      - (plusToMinusBlockMap (E := E) T).comp
          (((Dinv.symm : E ≃L[ℝ] E) : E →L[ℝ] E).comp
            (minusToPlusBlockMap (E := E) T))
      = (Schur : E →L[ℝ] E)

end Schur

section Berezinian

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Multiplicative Schur-complement Berezinian on admissible doubled transport. -/
noncomputable def generalizedBerezinian
    [FiniteDimensional ℝ E]
    (S : SchurAdmissibleTransport (E := E)) : ℝˣ :=
  Base.VolumeHom S.Schur.toLinearEquiv * (Base.VolumeHom S.Dinv.toLinearEquiv)⁻¹

/-- Positive scalar shadow of the Schur-complement Berezinian. -/
noncomputable def generalizedBerezinianScale
    [FiniteDimensional ℝ E]
    (S : SchurAdmissibleTransport (E := E)) : ℝ :=
  |((generalizedBerezinian (E := E) S : ℝˣ) : ℝ)|

/-- Diagonal shadow of a Schur-admissible doubled transport. -/
noncomputable def toRestrictedSheetEquiv
    (S : SchurAdmissibleTransport (E := E)) : RestrictedSheetEquiv E where
  plus := S.Schur.toLinearEquiv
  minus := S.Dinv.toLinearEquiv

@[simp] theorem generalizedBerezinian_eq_restrictedVolumeCharacter
    [FiniteDimensional ℝ E]
    (S : SchurAdmissibleTransport (E := E)) :
    generalizedBerezinian (E := E) S
      = RestrictedSheetEquiv.restrictedVolumeCharacter (E := E)
          (toRestrictedSheetEquiv (E := E) S) := by
  rfl

@[simp] theorem generalizedBerezinianScale_eq_restrictedVolumeScale
    [FiniteDimensional ℝ E]
    (S : SchurAdmissibleTransport (E := E)) :
    generalizedBerezinianScale (E := E) S
      = RestrictedSheetEquiv.restrictedVolumeScale (E := E)
          (toRestrictedSheetEquiv (E := E) S) := by
  rw [RestrictedSheetEquiv.restrictedVolumeScale_eq_abs_character]
  rfl

theorem schur_eq_plusBlock_of_offDiagonal_vanish
    (S : SchurAdmissibleTransport (E := E))
    (hPM : plusToMinusBlockMap (E := E) S.T = 0)
    (hMP : minusToPlusBlockMap (E := E) S.T = 0) :
    plusBlockMap (E := E) S.T = (S.Schur : E →L[ℝ] E) := by
  calc
    plusBlockMap (E := E) S.T
      = plusBlockMap (E := E) S.T
          - (plusToMinusBlockMap (E := E) S.T).comp
              (((S.Dinv.symm : E ≃L[ℝ] E) : E →L[ℝ] E).comp
                (minusToPlusBlockMap (E := E) S.T)) := by
          simp [hPM, hMP]
    _ = (S.Schur : E →L[ℝ] E) := S.hSchur

/-- If the off-diagonal blocks vanish, the Berezinian reduces to the flat restricted sheet ratio. -/
theorem generalizedBerezinian_diagonal_reduction
    [FiniteDimensional ℝ E]
    (S : SchurAdmissibleTransport (E := E))
    (hPM : plusToMinusBlockMap (E := E) S.T = 0)
    (hMP : minusToPlusBlockMap (E := E) S.T = 0) :
    plusBlockMap (E := E) S.T = (S.Schur : E →L[ℝ] E) ∧
      minusBlockMap (E := E) S.T = (S.Dinv : E →L[ℝ] E) ∧
      generalizedBerezinian (E := E) S
        = RestrictedSheetEquiv.restrictedVolumeCharacter (E := E)
            (toRestrictedSheetEquiv (E := E) S) := by
  refine ⟨schur_eq_plusBlock_of_offDiagonal_vanish (E := E) S hPM hMP, S.hD, ?_⟩
  exact generalizedBerezinian_eq_restrictedVolumeCharacter (E := E) S

end Berezinian

end InfoGeometry.Canonical.CartanBerezinianCore
