import Omega.OperatorAlgebra.FoldGroupoidMatrixUnitAutNormalizer

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-groupoid-matrixunit-normalizer`.

The conclusion-level normalizer statement is the packaged operator-algebra matrix-unit
normalizer theorem. -/
theorem paper_conclusion_fold_groupoid_matrixunit_normalizer
    (D : Omega.OperatorAlgebra.FoldGroupoidMatrixUnitAutNormalizerData)
    (foldRel_perm : ∀ i j, D.foldRel i j ↔ D.foldRel (D.perm i) (D.perm j)) :
    (∀ i j, D.foldRel i j →
      D.foldRel (D.matrixUnitImage i j).1 (D.matrixUnitImage i j).2) ∧
    (∀ i, D.recoveredPermutation i = D.perm i) ∧
    (∀ i j, D.foldRel i j ↔
      D.foldRel (D.recoveredPermutation i) (D.recoveredPermutation j)) := by
  exact Omega.OperatorAlgebra.paper_op_algebra_fold_groupoid_matrix_unit_aut_normalizer D foldRel_perm

end Omega.Conclusion
