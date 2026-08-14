import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

target = """      · intro hfixed
        have hfixed2 := hproj.mp hfixed
        have he : ∃ a : ℝˣ, a • x = hyperbolicFlowCoordinate t x := (Projectivization.mk_eq_mk_iff ℝ (hyperbolicFlowCoordinate t x) x hproj_aux hx).mp hfixed2
        rcases he with ⟨a, hax⟩
        have hc (i : Fin 8) : (a : ℝ) * x i =
            Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) * x i := by
          have hax' : a • x = hyperbolicFlowCoordinate t x := hax
          have hax'' := congrFun hax' i
          simpa [hyperbolicFlowCoordinate_apply, smul_eq_mul] using hax''.symm
        have kill (i : Fin 8) (c : ℝ) (he : (a : ℝ) ≠ c)"""

replacement = """      · intro hfixed
        have hfixed2 := hproj.mp hfixed
        have he : ∃ a : ℝ, a • x = hyperbolicFlowCoordinate t x := (Projectivization.mk_eq_mk_iff' ℝ (hyperbolicFlowCoordinate t x) x hproj_aux hx).mp hfixed2
        obtain ⟨a, hax⟩ := he
        have hc (i : Fin 8) : a * x i =
            Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) * x i := by
          have hax'' := congrFun hax i
          simpa [hyperbolicFlowCoordinate_apply, smul_eq_mul] using hax''.symm
        have kill (i : Fin 8) (c : ℝ) (he : a ≠ c)"""

text = text.replace(target, replacement)

# Also fix the ha' type
text = text.replace("have ha' : (a : ℝ) = Real.exp t", "have ha' : a = Real.exp t")
text = text.replace("have ha' : (a : ℝ) = Real.exp (-t)", "have ha' : a = Real.exp (-t)")

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

