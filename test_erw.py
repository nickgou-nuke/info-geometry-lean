import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

text = text.replace("rw [Matrix.mul_apply]", "erw [Matrix.mul_apply]")
text = text.replace("rw [PEquiv.toMatrix_mul_apply]", "erw [PEquiv.toMatrix_mul_apply]")
text = text.replace("rw [hpoint, hscaled, hsource]", "erw [hpoint, hscaled, hsource]")
text = text.replace("rw [dite_eq_left hpv]", "erw [dite_eq_left hpv]")
text = text.replace("rw [dite_eq_left hrow]", "erw [dite_eq_left hrow]")
text = text.replace("rw [dite_eq_left hcol]", "erw [dite_eq_left hcol]")
text = text.replace("rw [dite_eq_right hpv]", "erw [dite_eq_right hpv]")
text = text.replace("rw [dite_eq_right hrow]", "erw [dite_eq_right hrow]")
text = text.replace("rw [dite_eq_right hcol]", "erw [dite_eq_right hcol]")
text = text.replace("rw [dite_eq_left h_find]", "erw [dite_eq_left h_find]")

text = text.replace("simpa [findPivot, s] using h", "exact h")
text = text.replace("simpa [findPivot, s, htop] using h", "exact h")
text = text.replace("simpa using (Finset.coe_min' hs)", "exact Finset.coe_min' hs")

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
