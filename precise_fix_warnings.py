import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()

def replace_at(line_idx, old, new):
    if old in lines[line_idx-1]:
        lines[line_idx-1] = lines[line_idx-1].replace(old, new)

# L27: simpa [findPivot, s, htop] using h
replace_at(27, "simpa [findPivot, s, htop] using h", "simp only [findPivot, s, htop] at h\n    exact h")
replace_at(230, "simpa [ht] using hx", "simp only [ht] at hx\n    exact hx")

# Unused simp arguments
replace_at(498, "simp [hbp, hbp.symm]", "simp [hbp]")
replace_at(513, "simp [hbp, hbp.symm]", "simp [hbp]")
replace_at(530, "simp [hkp, hpivot]", "simp [hpivot]")
replace_at(532, "simp [hbk, hbk.symm]", "simp [hbk]")
replace_at(552, "simp [hbk, hbk.symm]", "simp [hbk]")
replace_at(579, "simp [hqk, hsource]", "simp [hsource]")
replace_at(581, "simp [hbk, hbk.symm]", "simp [hbk]")
replace_at(745, "simp [FixesRow]", "simp")
replace_at(1347, "simp only [ite_eq_left rfl]", "simp only")

# Unused variables (prefix with _)
replace_at(520, "(hkp : k ≠ pr)", "(_hkp : k ≠ pr)")
replace_at(862, "(hsource : A pi q = 0) (htarget : A i q = 0)", "(hsource : A pi q = 0) (_htarget : A i q = 0)")
replace_at(895, "(hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)", "(_hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)")
replace_at(926, "{q : Fin n} (hq : q.val < col)", "{q : Fin n} (_hq : q.val < col)")
replace_at(1212, "(hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)", "(_hfind : findPivot A pivotRow ⟨col, hcol⟩ = some pi)")

# Unused change tactic
replace_at(1074, "change (Erest * X) k c = X k c\n", "")
replace_at(1074, "change (Erest * X) k c = X k c", "")

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.writelines(lines)
