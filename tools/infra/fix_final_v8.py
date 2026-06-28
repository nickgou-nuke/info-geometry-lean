with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

header = """set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
"""

# Insert right after `set_option maxHeartbeats`
idx = text.find("set_option maxHeartbeats")
if idx != -1:
    end_idx = text.find("\\n", idx) + 1
    text = text[:end_idx] + header + text[end_idx:]

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
