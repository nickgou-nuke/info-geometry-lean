with open("lean/InfoGeometry/External/Automath/Omega/Zeta.lean", "r") as f:
    content = f.read()

with open("lean/InfoGeometry/External/Automath/Omega/Zeta.lean", "w") as f:
    f.write("/-\n" + content + "\n-/")
