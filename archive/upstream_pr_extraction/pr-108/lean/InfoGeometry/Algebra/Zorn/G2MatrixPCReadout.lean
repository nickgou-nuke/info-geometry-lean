import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

namespace InfoGeometry.Algebra.Zorn.G2MatrixPCReadout

open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-! Structural readouts of the PC matrix carrier.  These propositions package
the entry lemmas proved by row-support calculations; they do not enumerate
the Boolean coordinates. -/
def pcReadout (M : Matrix (Fin 8) (Fin 8) F2) : Prop :=
  M 2 2 = (1 : F2) ∧ M 3 3 = (1 : F2) ∧ M 7 2 = (0 : F2)

theorem matrixWord_pcReadout (e : PCExponent) :
    pcReadout (matrixWord e) := by
  exact ⟨matrixWord_entry_two_two e,
    matrixWord_entry_three_three e,
    matrixWord_entry_seven_two e⟩

theorem ne_of_pcReadout_entry
    {M N : Matrix (Fin 8) (Fin 8) F2}
    {i j : Fin 8}
    (hM : M i j = if i = j then (1 : F2) else 0)
    (hN : N i j ≠ if i = j then (1 : F2) else 0) :
    M ≠ N := by
  intro h
  apply hN
  rw [← h]
  exact hM

end InfoGeometry.Algebra.Zorn.G2MatrixPCReadout
