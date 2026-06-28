import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace decide with `fin_cases k <;> fin_cases b <;> fin_cases c <;> exact rfl`
# But wait, `bracket` contains `∑`, so `rfl` doesn't evaluate it by default if `rfl` hits a performance issue.
# Instead of `decide`, we can use `simp [sum_B_eval, bracket, Pi.single, Function.update, structConst]; norm_num`? No, that timed out!
# How did I compile this before? I compiled it before without the `sum_B_eval`!
# Let me just use `revert k c b; exact rfl`? No, `rfl` evaluates everything, let's see if it's faster.
# Actually, since we have `sum_B_eval`, we can use it with `simp`. The reason it timed out is maybe `norm_num` is slow on 625 terms.

text = text.replace("ext k; revert k b c; decide", "revert b c; decide")
text = text.replace("ext k; revert k hb c b; decide", "revert hb c b; decide")

# Wait, `decide` cannot evaluate `bracket` without unfolding it!
# I need to unfold it!

text = text.replace("revert b c; decide", "cases b <;> cases c <;> ext k <;> fin_cases k <;> rfl")
text = text.replace("revert hb c b; decide", "rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;> rfl")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
