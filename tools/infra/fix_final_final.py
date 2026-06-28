import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# 1. Fix set S to let S
text = text.replace("set S : Set OSp12", "let S : Set OSp12")

# 2. Fix maxHeartbeats
if "set_option maxHeartbeats 8000000" not in text:
    text = text.replace("set_option maxHeartbeats 800000", "set_option maxHeartbeats 8000000")

# 3. Fix the Universe constraints in the Sets
text = re.sub(r"have h1' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h1' : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by",
              text, flags=re.DOTALL)

text = re.sub(r"have h2' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h2' : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by",
              text, flags=re.DOTALL)

# Also fix `heven` and `hodd` in the extracted lemmas
text = text.replace("have heven : ({fun x => match x with | B.H => 1 | x => 0, fun x => match x with | B.Ep => 1 | x => 0, fun x => match x with | B.Em => 1 | x => 0} : Set OSp12)",
                    "have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12)")

text = text.replace("have hodd : ({fun x => match x with | B.G1 => 1 | x => 0, fun x => match x with | B.G2 => 1 | x => 0} : Set OSp12)",
                    "have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12)")

# 4. Make sure there are no raw `Pi.single H 1` inside `SuperLieRingInstance.lean`!
text = text.replace("{Pi.single H 1, Pi.single Ep 1, Pi.single Em 1}", "{Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)}")
text = text.replace("{Pi.single G1 1, Pi.single G2 1}", "{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}")

# 5. Fix `SuperBracket.lie_zero_right` to `.zero_lie`
text = text.replace("SuperBracket.lie_zero_right", "SuperBracket.zero_lie")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
