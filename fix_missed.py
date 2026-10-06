import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Fix L424
old_424 = """    simpa [selectedPivotStep] using
      (go_selected_pivot_eq (A := A) (pivotRow := pivotRow)
        (col := col) Es hcol hfind hrow)"""
new_424 = "    exact go_selected_pivot_eq (A := A) (pivotRow := pivotRow) (col := col) Es hcol hfind hrow"
text = text.replace(old_424, new_424)

# Fix L918
old_918 = """    simpa [selectedPivotStep, pr, j, A₁, pivotVal, A₂, Elims, E] using
      helim.trans hscale"""
new_918 = "    exact helim.trans hscale"
text = text.replace(old_918, new_918)

# Fix L1559
old_1559 = """      simpa only [pivotVal, A1, pr, j] using
        selected_pivotVal_ne_zero hcol hfind hpr"""
new_1559 = "      exact selected_pivotVal_ne_zero hcol hfind hpr"
text = text.replace(old_1559, new_1559)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
