import InfoGeometry.Optics.Cl11OperatorConjugationNorm

set_option autoImplicit false

/-!
# Projective ratios of non-null operator-valued `Cl(1,1)` coordinates

This module specializes the repository's noncommutative right projective ratio
to the units supplied by non-null `Cl(1,1)` coordinates.  The resulting
fractional expression is the second coordinate followed by Clifford
conjugation of the first, scaled by the inverse split norm.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorProjectiveRatio

open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.Cl11OperatorConjugationNorm
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

variable {W : Type*} [AddCommGroup W] [Module Complex W]

/-- The noncommutative projective ratio of two non-null `Cl(1,1)` operators is
right multiplication by the explicit conjugate-over-norm inverse. -/
theorem rightOperatorRatio_operatorCl11Unit
    (q r : Cl11) (hq : splitNorm q ≠ 0) (hr : splitNorm r ≠ 0) :
    rightOperatorRatio
        (operatorCl11Unit (W := W) q hq)
        (operatorCl11Unit (W := W) r hr) =
      operatorCl11 (W := W) r * operatorCl11InverseCandidate (W := W) q := by
  rfl

/-- Conjugate-over-norm formula for the projective ratio on the doubled
internal carrier. -/
theorem rightOperatorRatio_operatorCl11Unit_eq_smul
    (q r : Cl11) (hq : splitNorm q ≠ 0) (hr : splitNorm r ≠ 0) :
    rightOperatorRatio
        (operatorCl11Unit (W := W) q hq)
        (operatorCl11Unit (W := W) r hr) =
      ((splitNorm q : Complex)⁻¹) •
        operatorCl11 (W := W) (r * cliffordConjugate q) := by
  rw [rightOperatorRatio_operatorCl11Unit, operatorCl11InverseCandidate,
    mul_smul_comm, operatorCl11_mul]

/-- Pointwise projective readout on an operator-valued two-sheet state. -/
theorem rightOperatorRatio_operatorCl11Unit_apply
    (q r : Cl11) (hq : splitNorm q ≠ 0) (hr : splitNorm r ≠ 0)
    (ψ : Doubled W) (i : Fin 2) :
    rightOperatorRatio
        (operatorCl11Unit (W := W) q hq)
        (operatorCl11Unit (W := W) r hr) ψ i =
      ((splitNorm q : Complex)⁻¹) •
        operatorCl11 (W := W) (r * cliffordConjugate q) ψ i := by
  rw [rightOperatorRatio_operatorCl11Unit_eq_smul]
  rfl

/-- The same projective ratio expressed entirely through the public QGT
soldering map. -/
theorem rightOperatorRatio_QGTSoldering_cl11
    (q r : Cl11) (hq : splitNorm q ≠ 0) (hr : splitNorm r ≠ 0) :
    rightOperatorRatio
        (operatorCl11Unit (W := W) q hq)
        (operatorCl11Unit (W := W) r hr) =
      ((splitNorm q : Complex)⁻¹) •
        InfoGeometry.Unified.QGTSoldering
          (cl11QGTFourVector (W := W) (r * cliffordConjugate q)) := by
  rw [rightOperatorRatio_operatorCl11Unit_eq_smul,
    QGTSoldering_cl11QGTFourVector]
  rfl

end InfoGeometry.Optics.Cl11OperatorProjectiveRatio
