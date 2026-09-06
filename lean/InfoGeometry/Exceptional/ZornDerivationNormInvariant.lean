import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

/-!
# Norm and null-cone readback for canonical Zorn derivation flows

These are finite-flow consequences of the native automorphism owner.  They do
not assert that an arbitrary derivation is square-zero or that its flow is a
JKO/backpropagation step.
-/

namespace InfoGeometry.Exceptional.ZornDerivationNormInvariant

open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

/- The former arbitrary-time determinant/null-cone claims have no owner in the
   current automorphism API.  The native multiplication law does support the
   following exact consequence. -/
theorem canonical_derivation_flow_preserves_square_zero
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ)
    (hX : X * X = 0) :
    zornFlowLinearEquiv D.1 t X * zornFlowLinearEquiv D.1 t X = 0 := by
  have hmul := zornFlow_preserves_mul D t X X
  rw [← hmul, hX]
  simp

end InfoGeometry.Exceptional.ZornDerivationNormInvariant
