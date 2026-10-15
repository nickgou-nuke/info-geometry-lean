import InfoGeometry.Exceptional.RealSplitAlbertFreudenthal
import InfoGeometry.Algebra.H3ZornAdjointProductIdentity

/-!
# Real Albert coordinate readback of the adjoint-product identity

This file transports the existing H3Zorn Jordan-adjoint contraction to the
repository's coordinate `RealAlbertMatrix` carrier.  The right hand side uses
the transported unit `fromH3 1`; it does not introduce a second matrix unit or
another Albert carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra.RealAlbertMatrix

open InfoGeometry.Algebra.RealAlbertH3ZornCarrierAlignment

/-- In the real 27-coordinate Albert carrier, multiplication by the quadratic
adjoint contracts to the cubic norm times the transported Jordan unit. -/
theorem mul_adjointQuad_eq_norm_smul_unit (X : RealAlbertMatrix) :
    RealAlbertMatrix.mul X (adjointQuad X) =
      RealAlbertMatrix.smul (normCubic X) (fromH3 (1 : H3Zorn ℝ)) := by
  apply equiv.injective
  change toH3 (RealAlbertMatrix.mul X (adjointQuad X)) =
    toH3 (RealAlbertMatrix.smul (normCubic X) (fromH3 (1 : H3Zorn ℝ)))
  have hto (Y : H3Zorn ℝ) : toH3 (fromH3 Y) = Y := by
    simpa [equiv, toH3, fromH3] using equiv.right_inv Y
  rw [toH3_mul, adjointQuad]
  rw [hto]
  rw [InfoGeometry.Algebra.h3zorn_jordan_mul_adjoint_eq_norm_one]
  rw [toH3_smul, hto]
  rfl

end InfoGeometry.Algebra.RealAlbertMatrix

end
