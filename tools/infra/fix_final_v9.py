with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Remove the bad header
text = text.replace("set_option linter.unnecessarySeqFocus false\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n", "")

# Insert them after imports
imports = "import InfoGeometry.Clifford.ConformalLieAlgebra55"
options = """

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
"""
text = text.replace(imports, imports + options)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
