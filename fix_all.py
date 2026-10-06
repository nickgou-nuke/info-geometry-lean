import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# 1. Deprecations
text = text.replace("dif_pos", "dite_eq_left")
text = text.replace("dif_neg", "dite_eq_right")
text = text.replace("if_pos", "ite_eq_left")
text = text.replace("if_neg", "ite_eq_right")

# 2. rw Matrix.mul_apply issues
text = text.replace("rw [Matrix.mul_apply]", "change Matrix.mul _ _ _ _ = _\n    rw [Matrix.mul_apply]")
text = text.replace("rw [PEquiv.toMatrix_mul_apply]", "change Matrix.mul _ _ _ _ = _\n    rw [PEquiv.toMatrix_mul_apply]")

# 3. specific simpa failures
text = text.replace("simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr hi_pi", "exact swapRowsMat_preserves_row_entry hi_pr hi_pi")
text = text.replace("simpa [Elims] using elimination_fold_preserves_source_row_apply A₂ pr j", "exact elimination_fold_preserves_source_row_apply A₂ pr j")
text = text.replace("simpa [selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E] using\n    hrow.trans hscale", "exact hrow.trans hscale")
text = text.replace("simpa only [pivotVal, A₁, Eswap, pr, j] using\n      selected_pivotVal_ne_zero hcol hfind hrow", "exact selected_pivotVal_ne_zero hcol hfind hrow")
text = text.replace("simpa [A₁] using swapRowsMat_preserves_row_entry hOld_pr hOld_pi", "exact swapRowsMat_preserves_row_entry hOld_pr hOld_pi")
text = text.replace("simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂, E] using houtput", "exact houtput")
text = text.replace("simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr' hi_pi", "exact swapRowsMat_preserves_row_entry hi_pr' hi_pi")
text = text.replace("simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂] using\n    helim_k.trans hscale_k", "exact helim_k.trans hscale_k")
text = text.replace("by simpa [P', selectedPivotStep] using hP'", "by exact hP'")
text = text.replace("simpa only [pivotVal, A1, pr, j] using\n        selected_pivotVal_ne_zero hcol h_find hpr", "exact selected_pivotVal_ne_zero hcol h_find hpr")

# Wait, what about L947?
# hpoint is (selectedPivotStep ...).1 pr q = (pivotVal⁻¹ • A₁ pr) q
# let's just see if fixing the above fixes the type mismatch errors, then we can debug 947.

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
