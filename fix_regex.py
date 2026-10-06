import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Replace all simpa only [pivotVal, A1, pr, j] using selected_pivotVal_ne_zero hcol h_find hpr (or hfind)
text = re.sub(
    r"simpa only \[pivotVal, A1, pr, j\] using\s+selected_pivotVal_ne_zero hcol h_?find hpr",
    r"exact selected_pivotVal_ne_zero hcol \g<0>",
    text
)
# Wait, \g<0> is the whole match!
# Let's do it safer:
text = re.sub(
    r"simpa only \[pivotVal, A1, pr, j\] using\s+selected_pivotVal_ne_zero hcol h_find hpr",
    r"exact selected_pivotVal_ne_zero hcol h_find hpr",
    text
)
text = re.sub(
    r"simpa only \[pivotVal, A1, pr, j\] using\s+selected_pivotVal_ne_zero hcol hfind hpr",
    r"exact selected_pivotVal_ne_zero hcol hfind hpr",
    text
)

# And what about L876, 915, 918, 947, 987, 1187, 1208, 1241, 1263, 1323, 1399, 1552?
# Let's run my make_final_fix again on a pristine HEAD, BUT with the erw for the remaining rw that failed.
