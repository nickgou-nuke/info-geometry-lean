import InfoGeometry.Lie.CanonicalZornDerivationExponential
import Mathlib.Algebra.Group.End

/-!
# Canonical Zorn derivation one-parameter group

This module packages the additive flow identities for canonical Zorn
derivations, parameterized by the repository-owned `canonicalZornDerivations`
Lie subalgebra.
-/

namespace InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup

variable (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)

/-- Pointwise one-parameter group law for a canonical Zorn derivation. -/
theorem zornFlow_add_apply
    (s t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 (s + t) X =
      InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 s
        (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 t X) := by
  exact InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv_add_apply D.1 s t X

/-- Negative time of the Zorn flow inverts the positive-time flow. -/
@[simp]
theorem zornFlow_apply_neg_flow
    (t : ℝ)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 t
        (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv D.1 (-t) X) =
      X := by
  exact InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv_neg_apply D.1 t X

end InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
