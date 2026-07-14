noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-! ## 7. Relative determinant/scattering MBK target -/

/--
Relative determinant/scattering packet for the MBK program.

This is the narrow next target after the finite Majorana/Witten-character
layers.  It asks for one real self-adjoint relative MBK operator together with
the analytic data needed to identify its relative determinant or scattering
trace with the completed critical-line readout `Xi(t) = xi(1/2 + it)`.

All hard analytic assertions are fields.  In particular, this structure does
not construct the operator, prove a Fredholm determinant identity, prove the
Riemann--Weil explicit formula, or prove RH.
-/
structure RelativeMBKDeterminantScatteringPacket
    (Operator ScatteringMatrix DeterminantReadout : Type) where
  diracCutoff : Operator
  diracFree : Operator
  relativeDeterminant : DeterminantReadout
  scatteringPhase : ScatteringMatrix

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
