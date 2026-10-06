import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Fix unused simp arguments based on the warning lines
text = text.replace("simp only [hcol, ite_true, ite_eq_left]", "simp only [hcol, ite_true]")
text = text.replace("simp only [ite_eq_left rfl]", "simp only")
text = text.replace("simp [hbp, hbp.symm]", "simp [hbp]")
text = text.replace("simp [hkp, hpivot]", "simp [hpivot]")
text = text.replace("simp [hbk, hbk.symm]", "simp [hbk]")
text = text.replace("simp [hqk, hsource]", "simp [hsource]")
text = text.replace("simp [FixesRow]", "simp")

# Unused variables (prefix with _)
text = text.replace("(hkp : k ≠ pr)", "(_hkp : k ≠ pr)")
text = text.replace("(hsource : A pi q = 0) (htarget : A i q = 0)", "(hsource : A pi q = 0) (_htarget : A i q = 0)")
text = text.replace("(hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)", "(_hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)")
text = text.replace("{q : Fin n} (hq : q.val < col)", "{q : Fin n} (_hq : q.val < col)")

# Unused change tactic
text = text.replace("change (Erest * X) k c = X k c\n", "")

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
