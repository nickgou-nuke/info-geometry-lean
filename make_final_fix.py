import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Deprecations
text = text.replace("dif_pos", "dite_eq_left")
text = text.replace("dif_neg", "dite_eq_right")
text = text.replace("if_pos", "ite_eq_left")
text = text.replace("if_neg", "ite_eq_right")
text = text.replace("if_true", "ite_true")

# rw to erw
text = text.replace("rw [Matrix.mul_apply]", "erw [Matrix.mul_apply]")
text = text.replace("rw [PEquiv.toMatrix_mul_apply]", "erw [PEquiv.toMatrix_mul_apply]")
text = text.replace("rw [hpoint, hscaled, hsource]", "erw [hpoint, hscaled, hsource]")
text = text.replace("rw [dite_eq_left hpv]", "erw [dite_eq_left hpv]")
text = text.replace("rw [dite_eq_left hrow]", "erw [dite_eq_left hrow]")
text = text.replace("rw [dite_eq_left hcol]", "erw [dite_eq_left hcol]")
text = text.replace("rw [dite_eq_right hpv]", "erw [dite_eq_right hpv]")
text = text.replace("rw [dite_eq_right hrow]", "erw [dite_eq_right hrow]")
text = text.replace("rw [dite_eq_right hcol]", "erw [dite_eq_right hcol]")

# exact replacements for simpa
# We replace ONLY the simpa calls that were giving Type mismatch!
bad_simpas = [
    ("simpa [findPivot, s] using h", "exact h"),
    ("simpa using (Finset.coe_min' hs)", "exact Finset.coe_min' hs"),
    ("simpa [A₁] using swapRowsMat_preserves_row_entry hp_pr hp_pi", "exact swapRowsMat_preserves_row_entry hp_pr hp_pi"),
    ("simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr hi_pi", "exact swapRowsMat_preserves_row_entry hi_pr hi_pi"),
    ("simpa [Elims] using elimination_fold_preserves_source_row_apply A₂ pr j", "exact elimination_fold_preserves_source_row_apply A₂ pr j"),
    ("simpa [selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E] using\n    hrow.trans hscale", "exact hrow.trans hscale"),
    ("simpa only [pivotVal, A₁, Eswap, pr, j] using\n      selected_pivotVal_ne_zero hcol hfind hrow", "exact selected_pivotVal_ne_zero hcol hfind hrow"),
    ("simpa [A₁] using swapRowsMat_preserves_row_entry hOld_pr hOld_pi", "exact swapRowsMat_preserves_row_entry hOld_pr hOld_pi"),
    ("simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂, E] using houtput", "exact houtput"),
    ("simpa [A₁] using swapRowsMat_preserves_row_entry hi_pr' hi_pi", "exact swapRowsMat_preserves_row_entry hi_pr' hi_pi"),
    ("simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂] using\n    helim_k.trans hscale_k", "exact helim_k.trans hscale_k"),
    ("by simpa [P', selectedPivotStep] using hP'", "by exact hP'"),
    ("simpa only [pivotVal, A1, pr, j] using\n        selected_pivotVal_ne_zero hcol h_find hpr", "exact selected_pivotVal_ne_zero hcol h_find hpr"),
    ("simpa only [pivotVal, A1, pr, j] using\n      selected_pivotVal_ne_zero hcol h_find hpr", "exact selected_pivotVal_ne_zero hcol h_find hpr"),
]

for old, new in bad_simpas:
    text = text.replace(old, new)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
