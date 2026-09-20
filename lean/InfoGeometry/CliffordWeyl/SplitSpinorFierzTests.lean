import InfoGeometry.CliffordWeyl.SplitSpinorFierz

namespace InfoGeometry.CliffordWeyl.SplitSpinorFierz.Tests

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordWeyl.SplitCliffordGrades
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

example : Module.finrank ℝ (Clsplit 0) = 1 := by
  rw [clifford_finrank]

example : Module.finrank ℝ (Clsplit 2) = 16 := by
  rw [clifford_finrank]

example : Module.finrank ℝ (⋀[ℝ]^2 (InfoGeometry.CliffordTower.SplitSpace 2)) = 6 := by
  rw [degree_finrank]

example : Module.finrank ℝ (⋀[ℝ]^5 (InfoGeometry.CliffordTower.SplitSpace 2)) = 0 :=
  degree_finrank_above_dimension 2 5 (by decide)

example (stages : ℕ) : Function.Bijective (spinorEquiv stages) :=
  (spinorEquiv stages).bijective

example (stages : ℕ) (metric : SpinorMatrix stages) (left right : SpinorSpace stages) :
    ∑ blade, channelCoefficient stages metric left right blade • channelBasis stages blade =
      solder metric left right :=
  all_grade_fierz_reconstruction stages metric left right

#print axioms all_grade_fierz_reconstruction
#print axioms all_grade_fierz_product
#print axioms spinorEquiv

end InfoGeometry.CliffordWeyl.SplitSpinorFierz.Tests
