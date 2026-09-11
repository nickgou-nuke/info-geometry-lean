import InfoGeometry.Canonical.SplitG2DiscreteCalibration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GradedRationalCohomologyShadow

namespace InfoGeometry.Canonical

/-!
  Cohomological shadow of the finite split-`G₂` calibration layer.

  The construction is deliberately native: it uses the repository's cellular
  coboundary and the generic graded cycle/boundary quotient.  No smooth
  manifold, Hodge theorem, or analytic representative is asserted here.
-/

abbrev splitG2CellDifferential (K : FiniteOrientedCellComplex) :
    GradedRationalDifferential (RationalColorCochain K) :=
  cellularRationalDifferential K

abbrev splitG2ThreeCohomology (K : FiniteOrientedCellComplex) :=
  gradedCohomologyShadow (splitG2CellDifferential K) 2

abbrev splitG2FourCohomology (K : FiniteOrientedCellComplex) :=
  gradedCohomologyShadow (splitG2CellDifferential K) 3

def splitG2PhiCycle
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    gradedCycleSubmodule (splitG2CellDifferential K) 3 :=
  ⟨C.phi, C.d_phi_zero⟩

def splitG2PsiCycle
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    gradedCycleSubmodule (splitG2CellDifferential K) 4 :=
  ⟨C.psi, C.d_psi_zero⟩

def splitG2PhiCohomologyClass
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    splitG2ThreeCohomology K :=
  Submodule.Quotient.mk (splitG2PhiCycle C)

def splitG2PsiCohomologyClass
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    splitG2FourCohomology K :=
  Submodule.Quotient.mk (splitG2PsiCycle C)

theorem splitG2PhiCycle_mem
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    (splitG2PhiCycle C : RationalColorCochain K 3) ∈
      gradedCycleSubmodule (splitG2CellDifferential K) 3 :=
  (splitG2PhiCycle C).property

theorem splitG2PsiCycle_mem
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    (splitG2PsiCycle C : RationalColorCochain K 4) ∈
      gradedCycleSubmodule (splitG2CellDifferential K) 4 :=
  (splitG2PsiCycle C).property

theorem splitG2Calibration_closed_classes
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K) :
    (splitG2PhiCohomologyClass C : splitG2ThreeCohomology K) =
        Submodule.Quotient.mk (splitG2PhiCycle C) ∧
      (splitG2PsiCohomologyClass C : splitG2FourCohomology K) =
        Submodule.Quotient.mk (splitG2PsiCycle C) :=
  ⟨rfl, rfl⟩

theorem splitG2ExactCohomologyClass_eq_zero
    (K : FiniteOrientedCellComplex)
    (p : ℕ) (x : RationalColorCochain K p) :
    Submodule.Quotient.mk
        (p := gradedBoundaryInCycles (splitG2CellDifferential K) p)
        (⟨rationalCoboundary K p x,
          (cellularRationalDifferential K).d_sq_zero p x⟩) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  simpa [gradedBoundaryInCycles, gradedBoundarySubmodule, splitG2CellDifferential] using
    (show rationalCoboundary K p x ∈
        gradedBoundarySubmodule (splitG2CellDifferential K) p from
      ⟨x, rfl⟩)

end InfoGeometry.Canonical
