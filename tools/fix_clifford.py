with open("scratch/clifford_action.lean", "r") as f:
    lines = f.readlines()

for i in range(len(lines)):
    if "rw [h]" in lines[i]:
        lines[i] = lines[i].replace("rw [h]", "exact congrArg Subtype.val h")

with open("scratch/clifford_action.lean", "w") as f:
    f.writelines(lines)
