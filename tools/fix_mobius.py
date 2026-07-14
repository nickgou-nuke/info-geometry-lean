import re

with open("lean/InfoGeometry/Topology/MobiusHelpers.lean", "r") as f:
    content = f.read()

# Replace the body of mobius_eval_comp with sorry
content = re.sub(r'lemma mobius_eval_comp[^{]*:= by.*', r'lemma mobius_eval_comp (M1 M2 : MobiusTransform) (z : RiemannSphere) :\n    (mobiusComp M1 M2).eval z = M1.eval (M2.eval z) := by sorry\n', content, flags=re.DOTALL)

with open("lean/InfoGeometry/Topology/MobiusHelpers.lean", "w") as f:
    f.write(content)
