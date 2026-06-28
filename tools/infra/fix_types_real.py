import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# 1. Force maxHeartbeats at the top
if "set_option maxHeartbeats" not in text:
    text = text.replace("import InfoGeometry.Clifford.ConformalLieAlgebra55", "import InfoGeometry.Clifford.ConformalLieAlgebra55\n\nset_option maxHeartbeats 8000000")

# 2. Fix the missing Set OSp12 types in the evenPart/oddPart rewrites
text = re.sub(r"have h1' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h1' : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by",
              text, flags=re.DOTALL)

text = re.sub(r"have h2' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h2' : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by",
              text, flags=re.DOTALL)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
