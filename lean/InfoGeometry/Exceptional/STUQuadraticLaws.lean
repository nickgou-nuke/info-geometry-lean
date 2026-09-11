import InfoGeometry.Exceptional.CubicJordanQuadraticLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.STUAdjointHomogeneity
import InfoGeometry.Exceptional.STUFreudenthalIdentity

/-!
# Quadratic-law package for the diagonal STU datum

This packages the already verified concrete STU identities into the reusable
`CubicJordanQuadraticLaws` interface.  It does not assert an Albert or
exceptional Lie-algebra identification.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Exceptional.Freudenthal

noncomputable def stuAdjointCrossLinear :
    STUCarrier →ₗ[ℝ] STUCarrier →ₗ[ℝ] STUCarrier :=
  LinearMap.mk₂ ℝ stuAdjointCross
    (fun x y z => stuAdjointCross_add_left x y z)
    (fun r x y => stuAdjointCross_smul_left r x y)
    (fun x y z => stuAdjointCross_add_right x y z)
    (fun r x y => stuAdjointCross_smul_right r x y)

theorem stuAdjointCrossLinear_apply (x y : STUCarrier) :
    stuAdjointCrossLinear x y = stuAdjointCross x y := rfl

noncomputable def stuQuadraticLaws :
    CubicJordanQuadraticLaws STU_Datum :=
  { cross := stuAdjointCrossLinear
    cross_eq_polarization := by
      intro x y
      rw [stuAdjointCrossLinear_apply]
      change stuAdjointCross x y =
        stuAdjointQuad (x + y) - stuAdjointQuad x - stuAdjointQuad y
      rw [stuAdjointQuad_add]
      module
    adjoint_smul := by
      intro r x
      simpa [STU_Datum] using stuAdjointQuad_smul r x
    norm_line := by
      intro r x y
      simp [STU_Datum, stuNormCubic, stuTraceBilin, stuAdjointQuad,
        Pi.smul_apply, Pi.add_apply]
      ring
    adjoint_adjoint := by
      intro x
      simpa [STU_Datum] using stuAdjointQuad_adjointQuad x }

@[simp] theorem stuQuadraticLaws_cross_apply
    (x y : STUCarrier) :
    stuQuadraticLaws.cross x y = stuAdjointCross x y := rfl

theorem stuQuadraticLaws_adjoint_cross_linearization
    (x y : STUCarrier) :
    stuAdjointCross (stuAdjointQuad x) (stuAdjointCross x y) =
      stuNormCubic x • y +
        stuTraceBilin (stuAdjointQuad x) y • x := by
  simpa [stuQuadraticLaws_cross_apply] using
    CubicJordanQuadraticLaws.adjoint_cross_linearization
      stuQuadraticLaws x y

theorem stuAdjointCross_comm (x y : STUCarrier) :
    stuAdjointCross x y = stuAdjointCross y x := by
  simpa [stuQuadraticLaws_cross_apply] using
    CubicJordanQuadraticLaws.cross_comm stuQuadraticLaws x y

theorem stuAdjointQuad_line (r : ℝ) (x y : STUCarrier) :
    stuAdjointQuad (x + r • y) =
      stuAdjointQuad x + r • stuAdjointCross x y +
        r ^ 2 • stuAdjointQuad y := by
  simpa [stuQuadraticLaws_cross_apply] using
    CubicJordanQuadraticLaws.adjoint_line stuQuadraticLaws r x y

theorem stuNormCubic_line (r : ℝ) (x y : STUCarrier) :
    stuNormCubic (x + r • y) =
      stuNormCubic x +
        r * stuTraceBilin (stuAdjointQuad x) y +
        r ^ 2 * stuTraceBilin (stuAdjointQuad y) x +
        r ^ 3 * stuNormCubic y := by
  simpa [STU_Datum] using
    (stuQuadraticLaws.norm_line r x y)

end InfoGeometry.Exceptional.STUDatum
