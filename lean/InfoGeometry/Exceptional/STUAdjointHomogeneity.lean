import InfoGeometry.Exceptional.STUDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Homogeneity readouts for the concrete STU cubic datum

These elementary identities are prerequisites for a genuine polarization of
the Freudenthal quartic.  They are proved for the native STU carrier only;
they do not promote the abstract `CubicJordanDatum` contract.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

theorem stuNormCubic_smul (r : ℝ) (x : STUCarrier) :
    stuNormCubic (r • x) = r ^ 3 * stuNormCubic x := by
  simp [stuNormCubic, Pi.smul_apply]
  ring

theorem stuAdjointQuad_smul (r : ℝ) (x : STUCarrier) :
    stuAdjointQuad (r • x) = r ^ 2 • stuAdjointQuad x := by
  funext i
  fin_cases i <;> simp [stuAdjointQuad, Pi.smul_apply]
  <;> ring

/-- The bilinear cross term in the polarization of the STU adjoint. -/
def stuAdjointCross (x y : STUCarrier) : STUCarrier :=
  ![x 1 * y 2 + y 1 * x 2,
    x 0 * y 2 + y 0 * x 2,
    x 0 * y 1 + y 0 * x 1]

theorem stuAdjointCross_swap (x y : STUCarrier) :
    stuAdjointCross x y = stuAdjointCross y x := by
  funext i
  fin_cases i <;> simp [stuAdjointCross]
  <;> ring

theorem stuAdjointCross_smul_left (r : ℝ) (x y : STUCarrier) :
    stuAdjointCross (r • x) y = r • stuAdjointCross x y := by
  funext i
  fin_cases i <;> simp [stuAdjointCross, Pi.smul_apply]
  <;> ring

theorem stuAdjointCross_smul_right (r : ℝ) (x y : STUCarrier) :
    stuAdjointCross x (r • y) = r • stuAdjointCross x y := by
  rw [stuAdjointCross_swap, stuAdjointCross_smul_left,
    stuAdjointCross_swap]

theorem stuAdjointCross_add_left (x y z : STUCarrier) :
    stuAdjointCross (x + y) z =
      stuAdjointCross x z + stuAdjointCross y z := by
  funext i
  fin_cases i <;> simp [stuAdjointCross, Pi.add_apply]
  <;> ring

theorem stuAdjointCross_add_right (x y z : STUCarrier) :
    stuAdjointCross x (y + z) =
      stuAdjointCross x y + stuAdjointCross x z := by
  funext i
  fin_cases i <;> simp [stuAdjointCross, Pi.add_apply]
  <;> ring

theorem stuAdjointQuad_add (x y : STUCarrier) :
    stuAdjointQuad (x + y) =
      stuAdjointQuad x + stuAdjointCross x y + stuAdjointQuad y := by
  funext i
  fin_cases i <;> simp [stuAdjointQuad, stuAdjointCross, Pi.add_apply]
  <;> ring

theorem stuNormCubic_add (x y : STUCarrier) :
    stuNormCubic (x + y) =
      stuNormCubic x + stuNormCubic y
        + stuTraceBilin (stuAdjointQuad x) y
        + stuTraceBilin (stuAdjointQuad y) x := by
  simp [stuNormCubic, stuTraceBilin, stuAdjointQuad, Pi.add_apply]
  ring

theorem stuTraceBilin_adjoint_self (x : STUCarrier) :
    stuTraceBilin (stuAdjointQuad x) x = 3 * stuNormCubic x := by
  simp [stuTraceBilin, stuAdjointQuad, stuNormCubic]
  ring

theorem stuTraceBilin_adjointCross (x y z : STUCarrier) :
    stuTraceBilin (stuAdjointCross y z) x =
      6 * stuNormTrilin x y z := by
  simp [stuTraceBilin, stuAdjointCross, stuNormTrilin]
  ring

theorem stuNormCubic_adjoint (x : STUCarrier) :
    stuNormCubic (stuAdjointQuad x) = (stuNormCubic x) ^ 2 := by
  simp [stuNormCubic, stuAdjointQuad]
  ring

@[simp] theorem stuAdjointQuad_zero :
    stuAdjointQuad (0 : STUCarrier) = 0 := by
  funext i
  fin_cases i <;> simp [stuAdjointQuad]

@[simp] theorem stuNormCubic_zero :
    stuNormCubic (0 : STUCarrier) = 0 := by
  simp [stuNormCubic]

end InfoGeometry.Exceptional.STUDatum
