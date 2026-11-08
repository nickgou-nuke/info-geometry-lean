import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannZetaEvidenceCorridor
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Arithmetic.RiemannHypothesisKreinColimitSpectralBridge
import InfoGeometry.Topology.ProjectiveCayleyZetaBridge
import InfoGeometry.Canonical.ApolloniusCriticalLineLeafBridge
import InfoGeometry.Quantum.ApolloniusFisherInformation
import InfoGeometry.SymmetricDomains.DikinMetriplectic
import InfoGeometry.Dynamics.ActualZetaSouriauFlowBridge
import InfoGeometry.Canonical.BerryKeatingSpectralDilationsCapstone
import InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator

/-!
# Riemann-zeta geometric/dynamical theorem corridor

This file extends the theorem-owned arithmetic/analytic corridor with exact
finite/projective/information-geometric statements that already exist in the
repository.  It deliberately distinguishes the existence of these structures
from the stronger claim that every adjacent item in a heuristic RH pipeline is
already an intertwining theorem.

In particular this file does not prove:
* Chentsov uniqueness for the Apollonius metric;
* a global zeta metriplectic cylinder whose transfer operator has zeta zeros as
  spectrum;
* Hilbert--Polya;
* a Weil explicit formula or GUE universality.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor

open Complex
open scoped LSeries.notation
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Arithmetic.RiemannHypothesisKreinColimitSpectral
open InfoGeometry.Topology.ProjectiveCayleyZetaBridge
open InfoGeometry.Projective.ApolloniusNatural
open InfoGeometry.Quantum.ApolloniusFisherInformation
open InfoGeometry.SymmetricDomains.DikinMetriplectic
open InfoGeometry.Dynamics.ActualZetaSouriauFlowBridge
open InfoGeometry.Canonical.BerryKeatingDilations
open InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

/-! ## Arithmetic semigroup and logarithmic derivative -/

/-- Minimal arithmetic semigroup carrier used by the prime/Euler lane.
This records only the multiplicative monoid structure of positive arithmetic;
it is not a new unique-factorization theorem. -/
abbrev ArithmeticSemigroup := ℕ

@[simp] theorem arithmeticSemigroup_mul_assoc (a b c : ArithmeticSemigroup) :
    (a * b) * c = a * (b * c) := by
  exact Nat.mul_assoc a b c

/-- The genuine von-Mangoldt Dirichlet series is the negative logarithmic
 derivative of the actual Riemann zeta function on `Re(s)>1`. -/
theorem vonMangoldt_eq_actualZetaLogDerivative
    {s : ℂ} (hs : 1 < s.re) :
    L ↗ArithmeticFunction.vonMangoldt s =
      actualRiemannZetaLogDerivative s := by
  exact vonMangoldt_LSeries_eq_actualRiemannZetaLogDerivative hs

/-- Möbius is the Dirichlet-convolution inverse of zeta. -/
theorem moebius_zeta_convolution_inverse :
    (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
      ArithmeticFunction ℤ) = 1 := by
  exact moebius_mul_zeta_eq_one

/-! ## Projective/Cayley geometry of the critical line -/

/-- The centered functional-equation reflection becomes multiplicative
 inversion under the Cayley transform. -/
theorem cayley_reflection_to_inversion (w : ℂ) :
    cayley (-w) = (cayley w)⁻¹ := by
  exact cayley_neg w

/-- The critical-line imaginary axis maps to the unit circle. -/
theorem cayley_critical_line_to_unit_circle (t : ℝ) :
    Complex.normSq
      (cayley (Complex.I * (t : ℂ))) = 1 := by
  exact cayley_critical_line_norm_sq t

/-- In the native Apollonius homogeneous chart, the projective ratio lies on
 the unit circle exactly on the zero-rapidity leaf `xi=0`. -/
theorem apollonius_unit_circle_iff_zero_leaf (xi theta : ℝ) :
    OnLeeYangCircle (projectiveRatio (apolloniusRay xi theta)) ↔
      xi = 0 := by
  exact projectiveRatio_apolloniusRay_unitCircle_iff_xi_zero xi theta

/-! ## Fisher / information-geometric potential -/

/-- The Apollonius Fisher quadratic form is strictly positive away from the
 singular point. -/
theorem apollonius_fisher_positive
    (st : ApolloniusState)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < apolloniusFisherQuadraticForm st v := by
  exact apollonius_fisher_pos_def st v hv

/-- On the critical leaf the native Apollonius Fisher metric reduces to
 `1/t^2` on each diagonal direction. -/
theorem apollonius_fisher_critical_leaf (t : ℝ) (ht : t ≠ 0) :
    let st : ApolloniusState :=
      ⟨1 / 2, t, by
        have h : (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 = t ^ 2 := by ring
        rw [h]
        exact sq_pos_of_ne_zero ht⟩
    apolloniusFisherMatrix st 0 0 =
        1 / t ^ 2 ∧
      apolloniusFisherMatrix st 1 1 =
        1 / t ^ 2 := by
  exact apollonius_fisher_critical_line_reduction t ht

/-- Native nonnegative relative-entropy/Bregman potential used by the
 metriplectic information-geometric lane. -/
theorem information_geometric_potential_nonnegative (x : ℝ) :
    0 ≤ Real.exp (-x) - 1 + x := by
  exact modular_surprisal_deficit_nonneg x

/-! ## Actual zeta gradient/metriplectic flow -/

/-- On the convergent real half-line, the zeta entropy-gradient readout is
 exactly the negative von-Mangoldt L-series real part. -/
theorem actual_zeta_entropy_gradient_eq_vonMangoldt
    {beta : ℝ} (hbeta : 1 < beta) :
    actualZetaEntropyGradient beta =
      -(L ↗ArithmeticFunction.vonMangoldt (beta : ℂ)).re := by
  exact actualZetaEntropyGradient_eq_neg_vonMangoldt hbeta

/-- The actual zeta scalar metriplectic flow field is nonnegative for
 nonnegative mobility on `beta>1`. -/
theorem actual_zeta_metriplectic_flow_nonnegative
    {kappa beta : ℝ} (hkappa : 0 ≤ kappa) (hbeta : 1 < beta) :
    0 ≤ actualZetaMetriplecticFlowField kappa beta := by
  exact actualZetaMetriplecticFlowField_nonnegative hkappa hbeta

/-! ## Dilation and unit-circle transport -/

/-- Berry--Keating dilation is a genuine one-parameter multiplicative flow. -/
theorem dilation_group_law (t1 t2 x : ℝ) :
    dilationFlow t1 (dilationFlow t2 x) = dilationFlow (t1 + t2) x := by
  exact dilationFlow_add t1 t2 x

/-- Under the repository's scale-exponent chart, dilation preserves the
 critical-line locus. -/
theorem dilation_preserves_critical_line (E t : ℝ) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine
      (InfoGeometry.Canonical.RindlerLogDeRhamPolya.scaleExponentOfEnergy
        ((Real.log
          (dilationFlow t (Real.exp E)) : ℝ) : ℂ)) := by
  exact dilationFlow_preserves_criticalLine_via_scaleExponent E t

/-- The same dilation chart transports to the unit-circle image. -/
theorem dilation_preserves_unit_circle (E t : ℝ) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnLeeYangCircle
      (InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity
        (InfoGeometry.Canonical.RindlerLogDeRhamPolya.scaleExponentOfEnergy
          ((Real.log
            (dilationFlow t (Real.exp E)) : ℝ) : ℂ))) := by
  exact dilationFlow_preserves_leeYangCircle_via_scaleExponent E t

/-! ## Transfer-operator structural surface -/

/-- The native Ruelle--Perron--Frobenius transfer operator fixes the constant
 one function for the uniform potential.  This is a structural transfer-
operator theorem, not a zeta spectral identification. -/
theorem uniform_transfer_preserves_one {n : ℕ}
    (w : BitWord n) :
    transferOperator uniformPotential
      (fun _ => 1) w = 1 := by
  exact transfer_uniform_constant w

/-- Compact packet of the genuinely connected geometric/dynamical theorems.
It intentionally does not package a Hilbert--Polya implication. -/
theorem geometric_dynamical_packet
    (w : ℂ) (t xi theta : ℝ) :
    InfoGeometry.Topology.ProjectiveCayleyZetaBridge.cayley (-w) =
        (InfoGeometry.Topology.ProjectiveCayleyZetaBridge.cayley w)⁻¹ ∧
    Complex.normSq
        (InfoGeometry.Topology.ProjectiveCayleyZetaBridge.cayley
          (Complex.I * (t : ℂ))) = 1 ∧
    (OnLeeYangCircle (projectiveRatio (apolloniusRay xi theta)) ↔
      xi = 0) ∧
    0 ≤ Real.exp (-t) - 1 + t := by
  exact ⟨cayley_reflection_to_inversion w,
    cayley_critical_line_to_unit_circle t,
    apollonius_unit_circle_iff_zero_leaf xi theta,
    information_geometric_potential_nonnegative t⟩

end InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor

end noncomputable section
