import Mathlib

import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

noncomputable section

namespace InfoGeometry.Canonical.OperatorSurprisalSupertraceBridge

open Matrix
open InfoGeometry.NCG
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev GradedHilbert (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  FinKetSpace (ι ⊕ ι)
abbrev GradedOperator (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  GradedHilbert ι →L[ℂ] GradedHilbert ι
abbrev SectorMatrix (ι : Type*) := Matrix ι ι ℂ

theorem stateSurprisal_superTrace_of_blockDiagonal
    (ρ : GradedOperator ι) (Kplus Kminus : SectorMatrix ι)
    (hblock : matrixOfOp (stateSurprisal ρ) =
        fromBlocks Kplus (0 : SectorMatrix ι) (0 : SectorMatrix ι) Kminus) :
    superTrace (matrixOfOp (stateSurprisal ρ)) =
      Matrix.trace Kplus - Matrix.trace Kminus := by
  rw [hblock]
  exact superTrace_blockDiag_eq Kplus Kminus

theorem neg_cfc_log_superTrace_of_blockDiagonal
    (ρ : GradedOperator ι) (Kplus Kminus : SectorMatrix ι)
    (hblock : matrixOfOp (-cfc Real.log ρ) =
      fromBlocks Kplus (0 : SectorMatrix ι) (0 : SectorMatrix ι) Kminus) :
    superTrace (matrixOfOp (-cfc Real.log ρ)) =
      Matrix.trace Kplus - Matrix.trace Kminus := by
  rw [hblock]
  exact superTrace_blockDiag_eq Kplus Kminus

end InfoGeometry.Canonical.OperatorSurprisalSupertraceBridge
