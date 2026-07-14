with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

import re

replacement = """      · rw [if_pos hd]
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
        have h1 : (to_proj (M.eval (some z'))).1 = (1 / (M.a * z' + M.b)) * (M_act (to_proj (some z'))).1 := by
          rw [if_pos hd]
          dsimp [to_proj, M_act]
          field_simp; ring
        have h2 : (to_proj (M.eval (some z'))).2 = (1 / (M.a * z' + M.b)) * (M_act (to_proj (some z'))).2 := by
          rw [if_pos hd]
          dsimp [to_proj, M_act]
          change (0 : ℂ) = 1 / (M.a * z' + M.b) * (M.c * z' + M.d * 1)
          have h_zero : M.c * z' + M.d * 1 = 0 := by
            calc M.c * z' + M.d * 1 = M.c * z' + M.d := by ring
                                    _ = 0 := hd
          rw [h_zero, mul_zero]
        exact ⟨one_div_ne_zero ha, ⟨h1, h2⟩⟩
      · rw [if_neg hd]
        use (1 / (M.c * z' + M.d))
        have h1 : (to_proj (M.eval (some z'))).1 = (1 / (M.c * z' + M.d)) * (M_act (to_proj (some z'))).1 := by
          rw [if_neg hd]
          dsimp [to_proj, M_act]
          field_simp; ring
        have h2 : (to_proj (M.eval (some z'))).2 = (1 / (M.c * z' + M.d)) * (M_act (to_proj (some z'))).2 := by
          rw [if_neg hd]
          dsimp [to_proj, M_act]
          field_simp; ring
        exact ⟨one_div_ne_zero hd, ⟨h1, h2⟩⟩"""

match = re.search(r"      · rw \[if_pos hd\].*?exact ⟨h1, h2⟩\n      · rw \[if_neg hd\].*?          · field_simp; ring", content, re.DOTALL)
if match:
    content = content[:match.start()] + replacement + content[match.end():]

# Let's also fix the `none` branch similarly, just in case!
rep_none = """      dsimp [MobiusTransform.eval, to_proj, M_act]
      by_cases hc : M.c = 0
      · rw [if_pos hc]
        use (1 / M.a)
        have ha : M.a ≠ 0 := by
          intro h
          have : M.a * M.d - M.b * M.c = 0 := by rw [h, hc]; ring
          exact M.det_ne_zero this
        have h1 : (to_proj (if M.c = 0 then none else some (M.a / M.c))).1 = (1 / M.a) * (M.a * 1 + M.b * 0) := by
          rw [if_pos hc]
          dsimp [to_proj]
          field_simp; ring
        have h2 : (to_proj (if M.c = 0 then none else some (M.a / M.c))).2 = (1 / M.a) * (M.c * 1 + M.d * 0) := by
          rw [if_pos hc]
          dsimp [to_proj]
          change (0 : ℂ) = 1 / M.a * (M.c * 1 + M.d * 0)
          have h_zero : M.c * 1 + M.d * 0 = 0 := by
            calc M.c * 1 + M.d * 0 = M.c := by ring
                                   _ = 0 := hc
          rw [h_zero, mul_zero]
        exact ⟨one_div_ne_zero ha, ⟨h1, h2⟩⟩
      · rw [if_neg hc]
        use (1 / M.c)
        have h1 : (to_proj (if M.c = 0 then none else some (M.a / M.c))).1 = (1 / M.c) * (M.a * 1 + M.b * 0) := by
          rw [if_neg hc]
          dsimp [to_proj]
          field_simp; ring
        have h2 : (to_proj (if M.c = 0 then none else some (M.a / M.c))).2 = (1 / M.c) * (M.c * 1 + M.d * 0) := by
          rw [if_neg hc]
          dsimp [to_proj]
          field_simp; ring
        exact ⟨one_div_ne_zero hc, ⟨h1, h2⟩⟩"""

match_none = re.search(r"      dsimp \[MobiusTransform.eval, to_proj, M_act\].*?          · rw \[hc\]; field_simp; ring\n      · rw \[if_neg hc\].*?          · rw \[hc\]; field_simp; ring", content, re.DOTALL)
if match_none:
    content = content[:match_none.start()] + rep_none + content[match_none.end():]

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
