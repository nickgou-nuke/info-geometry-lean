import re

content = open("lean/InfoGeometry/Canonical/HestenesBivectorSelfDuality.lean").read()

content = content.replace("simp only [neg_smul, sub_eq_add_neg]", "simp only [sub_eq_add_neg]; rw [← neg_smul, neg_mul_eq_neg_mul]")

open("lean/InfoGeometry/Canonical/HestenesBivectorSelfDuality.lean", "w").write(content)
