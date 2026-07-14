import re

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

content = content.replace("rw [hc]; field_simp; ring", "try rw [hc]\n            field_simp; ring")
content = content.replace("rw [hd]; field_simp; ring", "try rw [hd]\n            field_simp; ring")
content = content.replace("pu.1 = Lu * (M_act u).1", "pu.1 = Lu * (M_act (u.1, u.2)).1")
content = content.replace("pu.2 = Lu * (M_act u).2", "pu.2 = Lu * (M_act (u.1, u.2)).2")
content = content.replace("pv.1 = Lv * (M_act v).1", "pv.1 = Lv * (M_act (v.1, v.2)).1")
content = content.replace("pv.2 = Lv * (M_act v).2", "pv.2 = Lv * (M_act (v.1, v.2)).2")

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
