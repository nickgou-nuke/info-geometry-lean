with open("sandbox/MajoranaPolyaHilbertSocket.lean", "r") as f:
    lines = f.readlines()

new_lines = []
for line in lines:
    if line.startswith("def concreteMajoranaPolyaHilbertBridge"):
        new_lines.append("def concreteMajoranaPolyaHilbertBridge : MajoranaPolyaHilbertBridge " + " ".join(["Unit"] * 32) + " := sorry\n")
    elif line.startswith("def concreteMajoranaBKTraceFormulaBridge"):
        new_lines.append("def concreteMajoranaBKTraceFormulaBridge : MajoranaBKTraceFormulaBridge " + " ".join(["Unit"] * 32) + " := sorry\n")
    elif line.startswith("def concreteMBKAnalyticFrontier"):
        new_lines.append("def concreteMBKAnalyticFrontier : MBKAnalyticFrontier " + " ".join(["Unit"] * 33) + " := sorry\n")
    else:
        new_lines.append(line)

with open("sandbox/MajoranaPolyaHilbertSocket.lean", "w") as f:
    f.writelines(new_lines)
