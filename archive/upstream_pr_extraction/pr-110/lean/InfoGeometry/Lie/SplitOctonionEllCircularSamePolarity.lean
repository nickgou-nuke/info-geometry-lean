import InfoGeometry.Lie.SplitOctonionEllPolarization
import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading

/-!
# A native same-polarity product witness

This owner records the concrete nonzero product needed to distinguish the
axial grading from a multiplicative derivation.  The calculation is confined
to one native Zorn coordinate; no associativity claim is used.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CanonicalZorn :=
  InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn

theorem rootPlus_zero_mul_rootPlus_one_ne_zero :
    rootPlus 0 * rootPlus 1 ≠ (0 : CanonicalZorn) := by
  intro h
  have hy := congrArg (fun Z : CanonicalZorn => Z.y 2) h
  simp [rootPlus, chiralNull, ellBasis, quaternionBasis, iUnit,
    jUnit, kQuaternionUnit, lUnit, zMul,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Equiv.smul_def,
    smul_eq_mul, InfoGeometry.Canonical.ZornMatrix.coordEquiv] at hy

end InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity
