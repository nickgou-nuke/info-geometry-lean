import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Restore from HEAD first to be safe, wait, I will just checkout HEAD and then run script.

# 1. Deprecations
text = text.replace("dif_pos", "dite_eq_left")
text = text.replace("dif_neg", "dite_eq_right")
text = text.replace("if_pos", "ite_eq_left")
text = text.replace("if_neg", "ite_eq_right")

# 2. Fix 658 by replacing the statement
text = text.replace("have h_add : (Equiv.swap pi pr).toPEquiv.toMatrix * A = FunctionalGaussJordan.swapRowsMat pr pi * A := by", "have h_add : Matrix.mul (Equiv.swap pi pr).toPEquiv.toMatrix A = FunctionalGaussJordan.swapRowsMat pr pi * A := by")

# Fix 696 by replacing the statement
text = text.replace("have h_oldRow : (Equiv.swap pi pr).toPEquiv.toMatrix * A k c = A oldRow c := by", "have h_oldRow : Matrix.mul (Equiv.swap pi pr).toPEquiv.toMatrix A k c = A oldRow c := by")

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

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
