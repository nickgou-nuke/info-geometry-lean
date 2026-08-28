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

theorem canonical_derivation_flow_preserves_norm
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ) :
    ZornMatrix.detZ (zornFlowLinearEquiv D.1 t X) = ZornMatrix.detZ X := by
  exact zornFlow_preserves_detZ D t X

theorem canonical_derivation_flow_preserves_null_cone
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ) :
    ZornMatrix.IsNull (zornFlowLinearEquiv D.1 t X) ↔
      ZornMatrix.IsNull X := by
  exact zornFlow_preserves_null D t X

theorem canonical_derivation_flow_preserves_square_zero
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ)
    (hX : X * X = 0) :
    zornFlowLinearEquiv D.1 t X * zornFlowLinearEquiv D.1 t X = 0 := by
  exact zornFlow_preserves_nilpotent D t X hX

end InfoGeometry.Exceptional.ZornDerivationNormInvariant
