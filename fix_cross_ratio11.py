with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

import re

replacement = """    | none =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hc : M.c = 0
      · rw [if_pos hc]
        use (1 / M.a)
        have ha : M.a ≠ 0 := by
          intro h
          have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
          exact M.det_ne_zero this
        refine ⟨one_div_ne_zero ha, ?_, ?_⟩
        · field_simp; ring
        · change (0 : ℂ) = 1 / M.a * (M.c * 1 + M.d * 0)
          have h_zero : M.c * 1 + M.d * 0 = 0 := by
            calc M.c * 1 + M.d * 0 = M.c := by ring
                                   _ = 0 := hc
          rw [h_zero, mul_zero]
      · rw [if_neg hc]
        use (1 / M.c)
        refine ⟨one_div_ne_zero hc, ?_, ?_⟩
        · field_simp; ring
        · field_simp; ring
    | some z' =>
      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hd : M.c * z' + M.d = 0
      · rw [if_pos hd]
        use (1 / (M.a * z' + M.b))
        have ha : M.a * z' + M.b ≠ 0 := by
          intro h
          have h1 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = 0 := by rw [h, hd]; ring
          have h2 : M.d * (M.a * z' + M.b) - M.b * (M.c * z' + M.d) = (M.a * M.d - M.b * M.c) * z' := by ring
          rw [h2] at h1
          have hz : z' = 0 := by
            cases mul_eq_zero.mp h1 with
            | inl hdet => exact (M.det_ne_zero hdet).elim
            | inr hz => exact hz
          rw [hz] at h hd
          have hb : M.b = 0 := by
            calc M.b = M.a * 0 + M.b := by ring
                 _ = 0 := h
          have hm_d : M.d = 0 := by
            calc M.d = M.c * 0 + M.d := by ring
                 _ = 0 := hd
          have hdet : M.a * M.d - M.b * M.c = 0 := by rw [hb, hm_d]; ring
          exact M.det_ne_zero hdet
        refine ⟨one_div_ne_zero ha, ?_, ?_⟩
        · field_simp; ring
        · change (0 : ℂ) = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1)
          have h_zero : M.c * z' + M.d * 1 = 0 := by
            calc M.c * z' + M.d * 1 = M.c * z' + M.d := by ring
                                    _ = 0 := hd
          rw [h_zero, mul_zero]
      · rw [if_neg hd]
        use (1 / (M.c * z' + M.d))
        refine ⟨one_div_ne_zero hd, ?_, ?_⟩
        · field_simp; ring
        · field_simp; ring"""

match = re.search(r"    \| none =>\n      dsimp \[MobiusTransform.eval, to_proj, M_act\].*?          field_simp; ring", content, re.DOTALL)
if match:
    content = content[:match.start()] + replacement + content[match.end():]

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
