import InfoGeometry.Algebra.H3ZornFreudenthalQuartic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornFreudenthalQuadraticLaws
import InfoGeometry.Exceptional.FreudenthalChargeLinear

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

theorem quarticInvariant_smul
    (r : ℝ) (Q : FreudenthalCharge (H3Zorn ℝ)) :
    quarticInvariant (r • Q) = r ^ 4 * quarticInvariant Q := by
  simp only [quarticInvariant, FreudenthalCharge.quarticInvariant,
    h3zornCubicJordanDatum,
    alpha_smul, beta_smul, x_smul, y_smul,
    H3Zorn.normCubic_smul, H3Zorn.adjointQuad_smul,
    H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
  simp [h3zornTraceBilin, H3Zorn.traceBilin_smul_left,
    H3Zorn.traceBilin_smul_right]
  ring

@[simp] theorem quarticInvariant_neg
    (Q : FreudenthalCharge (H3Zorn ℝ)) :
    quarticInvariant (-Q) = quarticInvariant Q := by
  have h := quarticInvariant_smul (-1 : ℝ) Q
  have hneg : (-Q) = (-1 : ℝ) • Q := by
    ext <;> simp [alpha_smul, beta_smul, x_smul, y_smul]
  rw [← hneg] at h
  convert h using 1 <;> norm_num

end InfoGeometry.Algebra.H3ZornFreudenthal
