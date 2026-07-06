with open("lean/InfoGeometry/Physics/ZornMatrixSU3.lean", "r") as f:
    content = f.read()

content = content.replace("simp [add_assoc_real]", "simp [add, zero, Pi.add_apply, add_assoc, add_left_comm, add_comm]")
content = content.replace("simp [add_comm_real]", "simp [add, zero, Pi.add_apply, add_assoc, add_left_comm, add_comm]")

with open("lean/InfoGeometry/Physics/ZornMatrixSU3.lean", "w") as f:
    f.write(content)
