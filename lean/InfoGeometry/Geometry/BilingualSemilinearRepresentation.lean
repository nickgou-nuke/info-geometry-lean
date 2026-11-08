import InfoGeometry.Geometry.BilingualUpperHalfPlane
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SemilinearPresentation

/-!
# Semilinear representation of bilingual doubled operators

This file connects the existing real-doubled bilingual operator trunk to
mathlib's semilinear-map surface.  The scalar transport is the identity
homomorphism on `ℝ`: the complex lane is represented by the doubled phase axis
`D.K`, and bilingual operators are precisely those commuting with that axis.
-/

namespace InfoGeometry.Geometry

open InfoGeometry.Canonical.SemilinearPresentation
open InfoGeometry.Quantum
open InfoGeometry.Krein

noncomputable section

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledEnd E

/-- A bounded real-linear doubled operator as a mathlib semilinear map. -/
@[rep_depth krein]
def operatorSemilinear (T : EndH) : H₂ →ₛₗ[(RingHom.id ℝ)] H₂ :=
  T.toLinearMap

omit [CompleteSpace E] in
@[simp]
theorem operatorSemilinear_apply (T : EndH) (v : H₂) :
    operatorSemilinear (E := E) T v = T v :=
  rfl

/-- The bilingual phase-linearity law as a semilinear readout equation. -/
@[rep_depth krein]
theorem operatorSemilinear_commutes_K_of_phaseLinear
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    {T : EndH} (hT : PhaseLinear D T) (v : H₂) :
    operatorSemilinear (E := E) T (D.K v) =
      D.K (operatorSemilinear (E := E) T v) := by
  exact PhaseLinear.map_K hT v

/-- The `τ` operator of a bilingual upper-half-plane point as a semilinear map. -/
@[rep_depth krein]
def bilingualTauSemilinear
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    (Z : BilingualUpperHalfPlane D) : H₂ →ₛₗ[(RingHom.id ℝ)] H₂ :=
  operatorSemilinear (E := E) Z.tau

@[simp]
theorem bilingualTauSemilinear_apply
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    (Z : BilingualUpperHalfPlane D) (v : H₂) :
    bilingualTauSemilinear (E := E) Z v = Z.tau v :=
  rfl

/-- Bilingual `τ` is semilinear and preserves the translated phase-axis readout. -/
@[rep_depth krein]
theorem bilingualTauSemilinear_commutes_K
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    (Z : BilingualUpperHalfPlane D) (v : H₂) :
    bilingualTauSemilinear (E := E) Z (D.K v) =
      D.K (bilingualTauSemilinear (E := E) Z v) := by
  exact operatorSemilinear_commutes_K_of_phaseLinear
    (E := E) Z.phase_linear v

omit [CompleteSpace E] in
/-- Phase-linear composition becomes composition of semilinear representations. -/
@[rep_depth krein]
theorem operatorSemilinear_comp_apply
    (S T : EndH) (v : H₂) :
    operatorSemilinear (E := E) (S.comp T) v =
      (operatorSemilinear (E := E) S).comp
        (operatorSemilinear (E := E) T) v :=
  rfl

end

end InfoGeometry.Geometry
