import InfoGeometry.Orthogonal.O55TwoBoundarySelection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Orthogonal.O55NativePinGradeReadout

/-! A native, type-correct two-boundary readout packet for the O(5,5) lane.

The matrix coefficient and its weight-selection rule live on `BoundaryPair55`.
The Pin involution is a separate geometric readout; this file only records
their common capstone and does not identify the two constructions.
-/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

theorem native_two_boundary_selection_packet
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k) :
    ((b : ℝ) - (a : ℝ) - (k : ℝ)) *
        B.bra ((A : End55) B.ket) = 0 ∧
      (B.readout (A : End55) ≠ 0 → b - a = k) := by
  constructor
  · exact homogeneous_matrix_coefficient_balance hv hf hA
  · intro hread
    exact contact_degree_of_nonzero_readout B hv hf hA hread

theorem native_pin_and_boundary_readout_packet
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k) :
    realSplitPinNullAction
          (fNegRealPin crosscapIndex)
          (nPairProjective crosscapIndex) =
        nbarPairProjective crosscapIndex ∧
      realSplitPinNullAction
          (fNegRealPin crosscapIndex)
          (nbarPairProjective crosscapIndex) =
        nPairProjective crosscapIndex ∧
      (((b : ℝ) - (a : ℝ) - (k : ℝ)) *
        B.bra ((A : End55) B.ket) = 0) := by
  exact ⟨native_pin_null_pair_swap,
    native_pin_null_pair_swap_back,
    (native_two_boundary_selection_packet B hv hf hA).1⟩

end InfoGeometry.Orthogonal.O55Contact
end noncomputable section
