import InfoGeometry.Canonical.SplitG2DiscreteCalibration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiscreteSplitOctonionStokes

namespace InfoGeometry.Canonical

/-!
# Boundary readouts for a finite split-`G₂` calibration

The calibration owner supplies closed rational `3`- and `4`-cochains.  This
file turns those equations into boundary observables using the existing
incidence boundary and finite Stokes pairing.  It is a cellular boundary
statement; it does not introduce a Dirichlet-to-Neumann operator or a smooth
boundary trace.
-/

noncomputable def phiBoundaryReadout
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K)
    (c : RationalCellChain K 4) : StandardSplitOctonionQ :=
  rationalCellPairing (rationalBoundary K 3 c) C.phi

noncomputable def psiBoundaryReadout
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K)
    (c : RationalCellChain K 5) : StandardSplitOctonionQ :=
  rationalCellPairing (rationalBoundary K 4 c) C.psi

theorem phiBoundaryReadout_eq_zero
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K)
    (c : RationalCellChain K 4) :
    phiBoundaryReadout C c = 0 := by
  unfold phiBoundaryReadout
  rw [← rationalStokes_pairing K 3 c C.phi]
  rw [C.d_phi_zero]
  simp [rationalCellPairing]

theorem psiBoundaryReadout_eq_zero
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K)
    (c : RationalCellChain K 5) :
    psiBoundaryReadout C c = 0 := by
  unfold psiBoundaryReadout
  rw [← rationalStokes_pairing K 4 c C.psi]
  rw [C.d_psi_zero]
  simp [rationalCellPairing]

theorem calibration_boundary_readouts_vanish
    {K : FiniteOrientedCellComplex}
    (C : SplitG2DiscreteCalibration K)
    (c₃ : RationalCellChain K 4)
    (c₄ : RationalCellChain K 5) :
    phiBoundaryReadout C c₃ = 0 ∧
      psiBoundaryReadout C c₄ = 0 :=
  ⟨phiBoundaryReadout_eq_zero C c₃, psiBoundaryReadout_eq_zero C c₄⟩

end InfoGeometry.Canonical
