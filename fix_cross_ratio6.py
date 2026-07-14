with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

replacement = """        constructor
        · exact one_div_ne_zero ha
        · have h1 : (match none with | none => (1, 0) | some z' => (z', 1)).1 = 1 / (M.a * z' + M.b) * (M.a * z' + M.b * 1) := by field_simp; ring
          have h2 : (match none with | none => (1, 0) | some z' => (z', 1)).2 = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1) := by
            calc 0 = M.c * z' + M.d := hd.symm
                 _ = z' * M.c + M.d := by ring
                 _ = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1) := by field_simp; ring
          exact ⟨h1, h2⟩"""

content = content.replace("""        constructor
        · exact one_div_ne_zero ha
        · constructor
          · field_simp; ring
          · have : z' * M.c + M.d = 0 := by
              calc z' * M.c + M.d = M.c * z' + M.d := by ring
              _ = 0 := hd
            rw [this]
            field_simp; ring""", replacement)

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
