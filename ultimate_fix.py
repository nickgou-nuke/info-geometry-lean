import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# 1. Deprecations
text = text.replace("dif_pos", "dite_eq_left")
text = text.replace("dif_neg", "dite_eq_right")
text = text.replace("if_pos", "ite_eq_left")
text = text.replace("if_neg", "ite_eq_right")
text = text.replace("if_true", "ite_true")

# 2. rw to erw
for old in [
    "rw [Matrix.mul_apply]",
    "rw [PEquiv.toMatrix_mul_apply]",
    "rw [hpoint, hscaled, hsource]",
    "rw [dite_eq_left hpv]",
    "rw [dite_eq_left hrow]",
    "rw [dite_eq_left hcol]",
    "rw [dite_eq_right hpv]",
    "rw [dite_eq_right hrow]",
    "rw [dite_eq_right hcol]",
    "rw [dite_eq_left hfind]",
    "rw [dite_eq_left h_find]"
]:
    text = text.replace(old, old.replace("rw [", "erw ["))

# 3. simpa replacements
# We will use regex to catch all of them robustly!

# simpa [findPivot, s] using h -> exact h
text = re.sub(r"simpa \[findPivot,\s*s\] using h", "exact h", text)

# simpa using (Finset.coe_min' hs) -> exact Finset.coe_min' hs
text = re.sub(r"simpa using \(Finset\.coe_min' hs\)", "exact Finset.coe_min' hs", text)

# simpa [A₁] using swapRowsMat_preserves_row_entry ... -> exact swapRowsMat_preserves_row_entry ...
text = re.sub(r"simpa \[A₁\] using swapRowsMat_preserves_row_entry (\S+) (\S+)", r"exact swapRowsMat_preserves_row_entry \1 \2", text)

# simpa [Elims] using elimination_fold_preserves_source_row_apply A₂ pr j
text = re.sub(r"simpa \[Elims\] using elimination_fold_preserves_source_row_apply A₂ pr j", "exact elimination_fold_preserves_source_row_apply A₂ pr j", text)

# simpa [selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E] using helim.trans hscale (or hrow.trans hscale)
text = re.sub(r"simpa \[selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E\] using\s+(hrow|helim)\.trans hscale", r"exact \1.trans hscale", text)

# simpa only [pivotVal, A₁, Eswap, pr, j] using selected_pivotVal_ne_zero hcol hfind hrow
text = re.sub(r"simpa only \[pivotVal, A₁, Eswap, pr, j\] using\s+selected_pivotVal_ne_zero hcol hfind hrow", "exact selected_pivotVal_ne_zero hcol hfind hrow", text)

# simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂, E] using houtput
text = re.sub(r"simpa \[selectedPivotStep, j, pr, A₁, pivotVal, A₂, E\] using houtput", "exact houtput", text)

# simpa [selectedPivotStep, j, pr, A₁, pivotVal, A₂] using helim_k.trans hscale_k
text = re.sub(r"simpa \[selectedPivotStep, j, pr, A₁, pivotVal, A₂\] using\s+helim_k\.trans hscale_k", "exact helim_k.trans hscale_k", text)

# by simpa [P', selectedPivotStep] using hP' -> by exact hP'
text = re.sub(r"by simpa \[P', selectedPivotStep\] using hP'", "by exact hP'", text)

# simpa only [pivotVal, A1, pr, j] using selected_pivotVal_ne_zero hcol h_find hpr (or hfind)
text = re.sub(r"simpa only \[pivotVal, A1, pr, j\] using\s+selected_pivotVal_ne_zero hcol (h_?find) hpr", r"exact selected_pivotVal_ne_zero hcol \1 hpr", text)

# go_selected_pivot_eq
text = re.sub(r"simpa \[selectedPivotStep\] using\s+\(go_selected_pivot_eq \(A := A\) \(pivotRow := pivotRow\)\s+\(col := col\) Es hcol hfind hrow\)", r"exact go_selected_pivot_eq (A := A) (pivotRow := pivotRow) (col := col) Es hcol hfind hrow", text)


with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
