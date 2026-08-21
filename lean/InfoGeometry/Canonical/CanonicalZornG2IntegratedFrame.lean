import InfoGeometry.Canonical.CanonicalZornDerivationExponential
import InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification

/-!
# Native integrated frame for the real split-Zorn `G₂` lane

This file is an integration owner, not a new algebraic model.  It combines
the existing kernel-checked declarations for the canonical derivation carrier
and its exponential flow at their common native type.  In particular, it does
not identify the real automorphism group with the finite group `G₂(2)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornG2IntegratedFrame

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Canonical.CanonicalZornDerivationExponential
open InfoGeometry.Lie.G2CartanSymmetricSpaceIdentification

local notation "CZ" => InfoGeometry.Lie.CanonicalZornDerivation.CZ

/-!
The following theorem is the native real split-Zorn integration point:
the 14-dimensional derivation carrier exponentiates to a one-parameter family
of product-, unit-, determinant-, and null-cone-preserving automorphisms.
-/
theorem canonical_g2_flow_frame
    (D : canonicalZornDerivations) (s t : ℝ) (X Y : CZ) :
    (Module.finrank ℝ canonicalZornDerivations = 14) ∧
      (zornFlowRealAut D (s + t) =
        zornFlowRealAut D s * zornFlowRealAut D t) ∧
      (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
          D.1 t (1 : CZ) = 1) ∧
      (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
          D.1 t (X * Y) =
        InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
            D.1 t X *
          InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
            D.1 t Y) ∧
      (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
            D.1 t X) =
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X) ∧
      (InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
          (InfoGeometry.Lie.CanonicalZornDerivationExponential.zornFlowLinearEquiv
            D.1 t X) ↔
        InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull X) := by
  refine ⟨g2Full_dim_eq_fourteen, zornFlowRealAut_add D s t,
    zornFlow_fixes_one D t, zornFlow_preserves_mul D t X Y, ?_, ?_⟩
  · exact zornFlow_preserves_detZ D t X
  · exact zornFlow_preserves_null D t X

end InfoGeometry.Canonical.CanonicalZornG2IntegratedFrame

end noncomputable section
