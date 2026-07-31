namespace Omega.OperatorAlgebra

/-- The standard fold-fiber decomposition and Schur-rigidity hypotheses imply the explicit
fiberwise commutant formula `span {I, J}`. -/
theorem paper_op_algebra_fold_gauge_commutant_explicit
    (foldFiberDecomposition globalToFiberwiseReduction
      scalarPlusOrthogonalDecomposition schurRigidityOnFibers
      fiberwiseCommutantIsSpanIJ : Prop)
    (foldFiberDecomposition_h : foldFiberDecomposition)
    (globalToFiberwiseReduction_h : globalToFiberwiseReduction)
    (scalarPlusOrthogonalDecomposition_h : scalarPlusOrthogonalDecomposition)
    (schurRigidityOnFibers_h : schurRigidityOnFibers)
    (deriveFiberwiseCommutantIsSpanIJ :
      foldFiberDecomposition → globalToFiberwiseReduction →
        scalarPlusOrthogonalDecomposition → schurRigidityOnFibers →
          fiberwiseCommutantIsSpanIJ) :
    fiberwiseCommutantIsSpanIJ := by
  exact deriveFiberwiseCommutantIsSpanIJ foldFiberDecomposition_h
    globalToFiberwiseReduction_h scalarPlusOrthogonalDecomposition_h
    schurRigidityOnFibers_h

end Omega.OperatorAlgebra
