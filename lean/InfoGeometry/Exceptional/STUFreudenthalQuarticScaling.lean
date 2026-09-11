import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.STUAdjointHomogeneity

/-!
# Quartic homogeneity for the native STU Freudenthal carrier

This is a concrete scaling law for the existing quartic invariant.  It is a
prerequisite for a later polarization argument and does not assert an
exceptional Lie-algebra identification.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Exceptional.Freudenthal

theorem stuQuarticInvariant_smul
    (r : ℝ) (Q : FreudenthalCharge STUCarrier) :
    FreudenthalCharge.quarticInvariant STU_Datum (r • Q) =
      r ^ 4 * FreudenthalCharge.quarticInvariant STU_Datum Q := by
  simp [FreudenthalCharge.quarticInvariant, STU_Datum,
    stuNormCubic_smul, stuAdjointQuad_smul, Pi.smul_apply]
  ring

theorem stuQuarticInvariant_neg (Q : FreudenthalCharge STUCarrier) :
    FreudenthalCharge.quarticInvariant STU_Datum (-Q) =
      FreudenthalCharge.quarticInvariant STU_Datum Q := by
  have h := stuQuarticInvariant_smul (-1 : ℝ) Q
  simpa [show (-1 : ℝ) ^ 4 = 1 by norm_num] using h

theorem stuQuarticInvariant_expanded
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalCharge.quarticInvariant STU_Datum Q =
      (Q.alpha * Q.beta -
        (Q.x 0 * Q.y 0 + Q.x 1 * Q.y 1 + Q.x 2 * Q.y 2)) ^ 2 -
      4 * (Q.alpha * (Q.x 0 * Q.x 1 * Q.x 2) +
        Q.beta * (Q.y 0 * Q.y 1 * Q.y 2) -
        ((Q.x 1 * Q.x 2) * (Q.y 1 * Q.y 2) +
          (Q.x 0 * Q.x 2) * (Q.y 0 * Q.y 2) +
          (Q.x 0 * Q.x 1) * (Q.y 0 * Q.y 1))) := by
  rfl

end InfoGeometry.Exceptional.STUDatum
