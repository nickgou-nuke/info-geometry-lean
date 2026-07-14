import Mathlib
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

/-!
# InfoGeometry.Arithmetic.CompletedXiProjectorBridge

Theorem-safe bridge from the existing completed-zeta antiunitary symmetry on
`ℂ` to the existing centered-chart Cartan projector calculus.

This file does NOT define the analytic completed ξ-function or prove RH.
Instead, it packages the exact content already supported by the owner files:

* `antiunitaryCriticalReflection` and its fixed-locus theorem on `ℂ`;
* centered zeta coordinates and the critical tangent/normal projectors.

Given a supplied completed-ξ anchor point fixed by the antiunitary reflection,
we prove that its centered chart lies entirely in the tangent (`J`-even) sector
and has zero normal (`J`-odd) component.
-/

namespace CompletedXiProjectorBridge

open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-- Read a complex spectral parameter in the centered zeta chart. -/
noncomputable def centeredOfComplex (s : ℂ) : ZetaCenteredChart :=
  toCentered (ofComplex s)

@[simp] theorem centeredOfComplex_u (s : ℂ) :
    (centeredOfComplex s).u = s.re - (1 / 2 : ℝ) := by
  simp [centeredOfComplex, toCentered, ofComplex, centeredSigma]

@[simp] theorem centeredOfComplex_v (s : ℂ) :
    (centeredOfComplex s).v = s.im := by
  rfl

/-- The antiunitary reflection on `ℂ` becomes the critical mirror on centered coordinates. -/
theorem centeredOfComplex_antiunitaryCriticalReflection (s : ℂ) :
    centeredOfComplex
        (CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s) =
      criticalMirror (centeredOfComplex s) := by
  apply ZetaCenteredChart.ext
  · simp [centeredOfComplex, toCentered, ofComplex, centeredSigma,
      CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection,
      criticalMirror]
    ring
  · simp [centeredOfComplex, toCentered, ofComplex,
      CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection,
      criticalMirror]

/-- A complex antiunitary fixed point becomes a centered critical-mirror fixed point. -/
theorem centered_fixed_of_complex_fixed
    {s : ℂ}
    (hs : CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s = s) :
    criticalMirror (centeredOfComplex s) = centeredOfComplex s := by
  rw [← centeredOfComplex_antiunitaryCriticalReflection, hs]

/-- Antiunitary fixed points lie on the critical line in centered coordinates. -/
theorem centered_u_eq_zero_of_complex_fixed
    {s : ℂ}
    (hs : CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s = s) :
    (centeredOfComplex s).u = 0 := by
  have hline : CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s :=
    (CompletedZetaSouriauDInfinityThermodynamics.fixed_antiunitaryCriticalReflection_iff_criticalLine s).mp hs
  simp [CompletedZetaSouriauDInfinityThermodynamics.CriticalLine,
    centeredOfComplex, toCentered, ofComplex, centeredSigma] at hline ⊢
  linarith

/-- For antiunitary fixed points, the critical tangent projector is the identity. -/
theorem criticalTangentProjector_eq_self_of_complex_fixed
    {s : ℂ}
    (hs : CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s = s) :
    criticalTangentProjector (centeredOfComplex s) = centeredOfComplex s := by
  apply ZetaCenteredChart.ext
  · exact (centered_u_eq_zero_of_complex_fixed hs).symm
  · simp [criticalTangentProjector, centeredOfComplex]

/-- For antiunitary fixed points, the critical normal projector vanishes. -/
theorem criticalNormalProjector_eq_zero_of_complex_fixed
    {s : ℂ}
    (hs : CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s = s) :
    criticalNormalProjector (centeredOfComplex s) = zero := by
  apply ZetaCenteredChart.ext
  · exact centered_u_eq_zero_of_complex_fixed hs
  · simp [criticalNormalProjector, zero]

/--
A theorem-safe completed-ξ projector packet.

`packet` is the existing completed-zeta Massieu shell; `anchor` is any supplied
spectral point whose completed-ξ realization is fixed by the antiunitary
critical reflection.
-/
structure CompletedXiProjectorPacket where
  packet : CompletedZetaMassieuPacket
  anchor : ℂ
  xi_anchor_fixed :
    CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection anchor = anchor

/-- The supplied anchor lies on the complex critical line. -/
theorem xi_anchor_on_criticalLine (P : CompletedXiProjectorPacket) :
    CompletedZetaSouriauDInfinityThermodynamics.CriticalLine P.anchor := by
  exact
    (CompletedZetaSouriauDInfinityThermodynamics.fixed_antiunitaryCriticalReflection_iff_criticalLine
      P.anchor).mp P.xi_anchor_fixed

/-- The supplied anchor is fixed by the centered critical mirror. -/
theorem xi_anchor_centered_fixed (P : CompletedXiProjectorPacket) :
    criticalMirror (centeredOfComplex P.anchor) = centeredOfComplex P.anchor :=
  centered_fixed_of_complex_fixed P.xi_anchor_fixed

/-- The supplied anchor lies entirely in the `J`-even/tangent sector. -/
theorem xi_anchor_tangent_projector_eq_self (P : CompletedXiProjectorPacket) :
    criticalTangentProjector (centeredOfComplex P.anchor) = centeredOfComplex P.anchor :=
  criticalTangentProjector_eq_self_of_complex_fixed P.xi_anchor_fixed

/-- The supplied anchor has zero `J`-odd/normal component. -/
theorem xi_anchor_normal_projector_eq_zero (P : CompletedXiProjectorPacket) :
    criticalNormalProjector (centeredOfComplex P.anchor) = zero :=
  criticalNormalProjector_eq_zero_of_complex_fixed P.xi_anchor_fixed

end CompletedXiProjectorBridge
