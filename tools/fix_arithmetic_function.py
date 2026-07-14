with open("lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean", "r") as f:
    content = f.read()

content = content.replace("Nat.ArithmeticFunction.vonMangoldt", "ArithmeticFunction.vonMangoldt")

with open("lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean", "w") as f:
    f.write(content)
