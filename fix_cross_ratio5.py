with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

replacement = """        constructor
        · exact one_div_ne_zero ha
        · constructor
          · field_simp; ring
          · have : z' * M.c + M.d = 0 := by
              calc z' * M.c + M.d = M.c * z' + M.d := by ring
              _ = 0 := hd
            rw [this]
            field_simp; ring"""

content = content.replace("""        constructor
        · exact one_div_ne_zero ha
        · constructor
          · field_simp; ring
          · field_simp; ring""", replacement)

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
