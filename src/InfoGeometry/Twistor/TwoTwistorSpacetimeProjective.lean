import InfoGeometry.Twistor.TwoTwistorSpacetimeNode
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.TwistorFrameCovariance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Projective frame invariance of the two-twistor node

The frame presentation uses columns of `P` for the lower spinors and columns
of `Ω` for their upper data.  A common invertible change of column frame sends
`(P, Ω)` to `(P * D, Ω * D)`.  This owner proves that the reconstructed complex
spacetime node is unchanged by that projective frame change.

This is only a finite matrix statement.  It does not impose Hermitian reality
or identify the complex node with a real Minkowski point.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwoTwistorSpacetimeProjective

open InfoGeometry.Twistor.TwoTwistorSpacetimeNode
open InfoGeometry.Twistor.TwistorFrameCovariance
open Matrix

theorem frameSpacetimeNode_right_rescale
    (P Ω D : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : IsUnit P.det) (hD : IsUnit D.det) :
    frameSpacetimeNode (P * D) (Ω * D) =
      frameSpacetimeNode P Ω := by
  have hPD : IsUnit (P * D).det := by
    rw [Matrix.det_mul]
    exact IsUnit.mul hP hD
  have hleft :
      (D⁻¹ * P⁻¹) * (P * D) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      (D⁻¹ * P⁻¹) * (P * D) =
          D⁻¹ * (P⁻¹ * P) * D := by simp [Matrix.mul_assoc]
      _ = D⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℂ) * D := by
        rw [Matrix.nonsing_inv_mul P hP]
      _ = D⁻¹ * D := by simp
      _ = 1 := Matrix.nonsing_inv_mul D hD
  have hinv : (P * D)⁻¹ = D⁻¹ * P⁻¹ :=
    Matrix.inv_eq_left_inv hleft
  change (-Complex.I) • ((Ω * D) * (P * D)⁻¹) =
    (-Complex.I) • (Ω * P⁻¹)
  rw [hinv]
  congr 1
  calc
    (Ω * D) * (D⁻¹ * P⁻¹) = Ω * (D * D⁻¹) * P⁻¹ := by
      noncomm_ring
    _ = Ω * P⁻¹ := by
      rw [Matrix.mul_nonsing_inv D hD]
      simp

theorem frameSpacetimeNode_left_covariant
    (A P Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A.det) (hP : IsUnit P.det) :
    frameSpacetimeNode (A * P) (A * Ω) =
      frameAction A (frameSpacetimeNode P Ω) := by
  have hAP : IsUnit (A * P).det := by
    rw [Matrix.det_mul]
    exact IsUnit.mul hA hP
  have hleft :
      (P⁻¹ * A⁻¹) * (A * P) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      (P⁻¹ * A⁻¹) * (A * P) =
          P⁻¹ * (A⁻¹ * A) * P := by simp [Matrix.mul_assoc]
      _ = P⁻¹ * (1 : Matrix (Fin 2) (Fin 2) ℂ) * P := by
        rw [Matrix.nonsing_inv_mul A hA]
      _ = P⁻¹ * P := by simp
      _ = 1 := Matrix.nonsing_inv_mul P hP
  have hinv : (A * P)⁻¹ = P⁻¹ * A⁻¹ :=
    Matrix.inv_eq_left_inv hleft
  change (-Complex.I) • ((A * Ω) * (A * P)⁻¹) =
    A * ((-Complex.I) • (Ω * P⁻¹)) * A⁻¹
  rw [hinv]
  simp [Matrix.mul_assoc]

end InfoGeometry.Twistor.TwoTwistorSpacetimeProjective
