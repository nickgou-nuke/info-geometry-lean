import re

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace("∀ u v Lu Lv pu pv,", "∀ (u v : ℂ × ℂ) (Lu Lv : ℂ) (pu pv : ℂ × ℂ),")
content = content.replace("try rw [hc]\n            field_simp; ring", "simp only [hc]; field_simp; ring")
content = content.replace("try rw [hd]\n            field_simp; ring", "simp only [hd]; field_simp; ring")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
