import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo

/-!
# Winding flux versus finite operator commutators

The repository already has a genuine topological quantization theorem: the
logarithmic one-form `dz / z` integrates to `2πi`, and an integer winding
multiplies this period by `n`.  This file gives that theorem a flux-oriented
readout and keeps it separate from finite-dimensional canonical commutators.

Thus the rigorous quantization mechanism used here is winding/residue
integrality.  It is not inferred from an impossible finite-dimensional exact
CCR, and no integer winding label is identified with a Riemann-zero ordinate.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusWindingFluxBridge

open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo

/-- Integer-winding flux of the logarithmic pole form on a circle of radius
`R`. -/
def quantizedWindingFlux (R : ℝ) (n : ℤ) : ℂ :=
  (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)

/-- The winding flux is the repository's logarithmic monodromy phase. -/
theorem quantizedWindingFlux_eq_logarithmicPhase
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    quantizedWindingFlux R n = logarithmicPhase n := by
  exact deRhamClass_of_winding R hR n

/-- Explicit `2πi n` quantization law. -/
theorem quantizedWindingFlux_eq_two_pi_mul_I
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    quantizedWindingFlux R n =
      (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  simp [quantizedWindingFlux, circleIntegral_one_div R hR]

/-- Winding flux is additive in the integer winding number. -/
theorem quantizedWindingFlux_add
    (R : ℝ) (hR : 0 < R) (m n : ℤ) :
    quantizedWindingFlux R (m + n) =
      quantizedWindingFlux R m + quantizedWindingFlux R n := by
  simp [quantizedWindingFlux, circleIntegral_one_div R hR,
    Int.cast_add]
  ring

/-- Exponentiating an integer-winding logarithmic flux gives trivial closed
holonomy. -/
theorem quantizedWindingHolonomy_eq_one
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp (quantizedWindingFlux R n) = 1 := by
  exact wilsonPhase_of_winding R hR n

/-- The rigorous winding quantization theorem and the finite canonical CCR
obstruction hold simultaneously: winding produces an integral period, while
no nonzero scalar identity can be a commutator on the native Zorn carrier. -/
theorem winding_quantization_with_finite_ccr_obstruction
    (R : ℝ) (hR : 0 < R) (n : ℤ)
    (A B : InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo.EndCZ)
    (c : ℝ) (hc : c ≠ 0) :
    quantizedWindingFlux R n = logarithmicPhase n ∧
      A * B - B * A ≠
        InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo.scalarOperator c := by
  exact ⟨quantizedWindingFlux_eq_logarithmicPhase R hR n,
    no_exact_nonzero_scalar_commutator A B c hc⟩

end InfoGeometry.Canonical.ApolloniusWindingFluxBridge
