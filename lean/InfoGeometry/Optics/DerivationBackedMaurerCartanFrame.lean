/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.NoncommutativeConnectionCurvature
import InfoGeometry.Optics.LocalGaugeFrameComposition

/-!
# Derivation-backed local gauge frames

Given a point- and direction-indexed family of algebra derivations and a
unit-valued frame, this file constructs the right logarithmic one-form
`D(u) * u⁻¹` used by the local gauge connection owner.  The construction is
algebraic: it proves the sign convention and product-frame cocycle in an
associative algebra.  It does not assert that arbitrary connections are pure
gauge, or that the supplied derivations arise from a manifold exterior
derivative.
-/

noncomputable section

namespace InfoGeometry.Optics.DerivationBackedMaurerCartanFrame

open InfoGeometry.NCG
open InfoGeometry.NCG.AlgebraDerivation
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.LocalGaugeFrameComposition

variable {R Point Tangent A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- A direction-indexed algebra derivation on the coefficient algebra. -/
abbrev DirectionalDerivation :=
  Point → Tangent → AlgebraDerivation R A

/-- Build the local right Maurer--Cartan frame from the logarithmic derivative
of a unit-valued frame, using the convention `theta = D(u) * u⁻¹`. -/
def fromDirectionalDerivation
    (D : DirectionalDerivation (R := R) (Point := Point)
      (Tangent := Tangent) (A := A))
    (u : Point → Aˣ) :
    RightMaurerCartanFrame (Point := Point) (Tangent := Tangent) (A := A) where
  frame := u
  theta p X := D p X (u p) * ((u p)⁻¹ : Aˣ).val

/-- The stored one-form is the negative of the NCG owner's
`u * D(u⁻¹)` convention, hence equals the right logarithmic derivative. -/
theorem theta_eq_neg_pureGaugeForm
    (D : DirectionalDerivation (R := R) (Point := Point)
      (Tangent := Tangent) (A := A))
    (u : Point → Aˣ) (p : Point) (X : Tangent) :
    (fromDirectionalDerivation D u).theta p X =
      - pureGaugeForm (D p X) (u p) := by
  rw [pureGaugeForm_eq_neg]
  simp [fromDirectionalDerivation]

/-- Right logarithmic differentiation obeys the same semidirect product law
as `composeRightFrames`, for a fixed derivation in each direction. -/
theorem rightLogDerivative_mul
    (D : AlgebraDerivation R A) (u v : Aˣ) :
    D ((u * v : Aˣ) : A) * (((u * v)⁻¹ : Aˣ) : A) =
      D (u : A) * ((u⁻¹ : Aˣ) : A) +
        (u : A) * (D (v : A) * ((v⁻¹ : Aˣ) : A)) * ((u⁻¹ : Aˣ) : A) := by
  calc
    D ((u * v : Aˣ) : A) * (((u * v)⁻¹ : Aˣ) : A) =
        (D (u : A) * (v : A) + (u : A) * D (v : A)) *
          ((v⁻¹ : Aˣ) : A) * ((u⁻¹ : Aˣ) : A) := by
            rw [Units.val_mul, mul_inv_rev, Units.val_mul, D.leibniz]
            noncomm_ring
    _ = D (u : A) * ((v : A) * ((v⁻¹ : Aˣ) : A)) *
          ((u⁻¹ : Aˣ) : A) +
        (u : A) * (D (v : A) * ((v⁻¹ : Aˣ) : A)) *
          ((u⁻¹ : Aˣ) : A) := by noncomm_ring
    _ = D (u : A) * ((u⁻¹ : Aˣ) : A) +
        (u : A) * (D (v : A) * ((v⁻¹ : Aˣ) : A)) *
          ((u⁻¹ : Aˣ) : A) := by rw [Units.mul_inv, mul_one]

/-- Pointwise multiplication of unit-valued frames is carried by the
semidirect composition already defined for local gauge frames. -/
theorem fromDirectionalDerivation_mul
    (D : DirectionalDerivation (R := R) (Point := Point)
      (Tangent := Tangent) (A := A))
    (u v : Point → Aˣ) :
    fromDirectionalDerivation D (fun p => u p * v p) =
      composeRightFrames (fromDirectionalDerivation D u)
        (fromDirectionalDerivation D v) := by
  apply congrArg₂ RightMaurerCartanFrame.mk
  · funext p
    rfl
  · funext p X
    exact rightLogDerivative_mul (D p X) (u p) (v p)

end InfoGeometry.Optics.DerivationBackedMaurerCartanFrame
