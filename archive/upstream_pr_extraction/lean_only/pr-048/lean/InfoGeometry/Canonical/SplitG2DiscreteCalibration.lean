import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
# Discrete split-`G₂` calibration data

This is the finite cellular layer between algebraic split-`G₂` witnesses and
any future smooth theory.  A calibration consists of rational split-octonion
3- and 4-cochains on a finite oriented cell complex, together with the closed
cochain equations.  The equations use the repository's incidence-based
`rationalCoboundary`; no differential manifold or analytic continuation is
introduced here.
-/

structure SplitG2DiscreteCalibration (K : FiniteOrientedCellComplex) where
  phi : RationalColorCochain K 3
  psi : RationalColorCochain K 4
  d_phi_zero : rationalCoboundary K 3 phi = 0
  d_psi_zero : rationalCoboundary K 4 psi = 0

namespace SplitG2DiscreteCalibration

theorem phi_closed
    {K : FiniteOrientedCellComplex} (C : SplitG2DiscreteCalibration K) :
    rationalCoboundary K 3 C.phi = 0 :=
  C.d_phi_zero

theorem psi_closed
    {K : FiniteOrientedCellComplex} (C : SplitG2DiscreteCalibration K) :
    rationalCoboundary K 4 C.psi = 0 :=
  C.d_psi_zero

theorem phi_coboundary_sq_zero
    {K : FiniteOrientedCellComplex} (C : SplitG2DiscreteCalibration K) :
    (rationalCoboundary K 4)
        (rationalCoboundary K 3 C.phi) = 0 := by
  rw [C.d_phi_zero]
  exact (rationalCoboundary K 4).map_zero

theorem psi_coboundary_sq_zero
    {K : FiniteOrientedCellComplex} (C : SplitG2DiscreteCalibration K) :
    (rationalCoboundary K 5)
        (rationalCoboundary K 4 C.psi) = 0 := by
  rw [C.d_psi_zero]
  exact (rationalCoboundary K 5).map_zero

theorem closed_pair
    {K : FiniteOrientedCellComplex} (C : SplitG2DiscreteCalibration K) :
    rationalCoboundary K 3 C.phi = 0 ∧
      rationalCoboundary K 4 C.psi = 0 :=
  ⟨C.d_phi_zero, C.d_psi_zero⟩

end SplitG2DiscreteCalibration

end InfoGeometry.Canonical
