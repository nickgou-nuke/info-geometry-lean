import InfoGeometry.Exceptional.STUDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# STU Freudenthal polarization

This owner records the finite polarization identity relating the existing STU
cubic trilinear form to the existing quadratic adjoint and trace pairing.  It
does not construct a Freudenthal triple system or identify an exceptional Lie
algebra.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Exceptional.Freudenthal

theorem stuNormTrilin_eq_adjoint_polarization
    (x y z : STUCarrier) :
    stuNormTrilin x y z =
      (1 / 6 : ℝ) *
        stuTraceBilin x
          (stuAdjointQuad (y + z) - stuAdjointQuad y - stuAdjointQuad z) := by
  dsimp [stuNormTrilin, stuTraceBilin, stuAdjointQuad]
  simp
  ring

end InfoGeometry.Exceptional.STUDatum
