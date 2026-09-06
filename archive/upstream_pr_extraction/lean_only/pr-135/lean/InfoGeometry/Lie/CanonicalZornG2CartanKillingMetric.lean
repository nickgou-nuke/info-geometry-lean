import InfoGeometry.Lie.CanonicalZornIsKilling

/-!
# Cartan--Killing metric surface for the canonical Zorn derivations

The metric is Mathlib's Killing bilinear form on the already verified
semisimple derivation algebra.  This file only exposes that owner-level form;
it does not introduce a coordinate matrix or a finite expansion.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanKillingMetric

open InfoGeometry.Lie.CanonicalZornIsKilling

abbrev Der := CanonicalZornIsKilling.Der

def cartanKillingMetric : LinearMap.BilinForm ℝ Der :=
  killingForm ℝ Der

theorem cartanKillingMetric_nondegenerate :
    cartanKillingMetric.Nondegenerate := by
  exact LieAlgebra.IsKilling.killingForm_nondegenerate ℝ Der

end InfoGeometry.Lie.CanonicalZornG2CartanKillingMetric
