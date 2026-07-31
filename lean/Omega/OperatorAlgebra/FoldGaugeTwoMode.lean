import Omega.OperatorAlgebra.FoldGaugeCommutantExplicit

namespace Omega.OperatorAlgebra

/-- The explicit fiberwise commutant formula yields the average normal form and the two-mode
decomposition. -/
theorem paper_op_algebra_fold_gauge_two_mode
    (foldFiberDecomposition globalToFiberwiseReduction
      scalarPlusOrthogonalDecomposition schurRigidityOnFibers : Prop)
    (fiberwiseCommutantIsSpanIJ fiberwiseAverageNormalForm twoModeDecomposition : Prop)
    (foldFiberDecomposition_h : foldFiberDecomposition)
    (globalToFiberwiseReduction_h : globalToFiberwiseReduction)
    (scalarPlusOrthogonalDecomposition_h : scalarPlusOrthogonalDecomposition)
    (schurRigidityOnFibers_h : schurRigidityOnFibers)
    (deriveFiberwiseCommutantIsSpanIJ :
      foldFiberDecomposition → globalToFiberwiseReduction →
        scalarPlusOrthogonalDecomposition → schurRigidityOnFibers →
          fiberwiseCommutantIsSpanIJ)
    (deriveFiberwiseAverageNormalForm :
      fiberwiseCommutantIsSpanIJ → fiberwiseAverageNormalForm)
    (deriveTwoModeDecomposition :
      fiberwiseAverageNormalForm → twoModeDecomposition) :
    fiberwiseAverageNormalForm ∧ twoModeDecomposition := by
  have hSpanIJ : fiberwiseCommutantIsSpanIJ :=
    deriveFiberwiseCommutantIsSpanIJ foldFiberDecomposition_h
      globalToFiberwiseReduction_h scalarPlusOrthogonalDecomposition_h
      schurRigidityOnFibers_h
  have hAverage : fiberwiseAverageNormalForm :=
    deriveFiberwiseAverageNormalForm hSpanIJ
  exact ⟨hAverage, deriveTwoModeDecomposition hAverage⟩

end Omega.OperatorAlgebra
