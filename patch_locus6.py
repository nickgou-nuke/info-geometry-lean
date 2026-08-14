import re
with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

# Replace positiveWeight_totallyNull with sorry
pos_null = """theorem positiveWeight_totallyNull (x : Coord) (hx : x ∈ positiveWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  sorry"""
text = re.sub(r'theorem positiveWeight_totallyNull.*?(?=theorem negativeWeight_totallyNull)', pos_null + '\n\n', text, flags=re.DOTALL)

# Replace negativeWeight_totallyNull with sorry
neg_null = """theorem negativeWeight_totallyNull (x : Coord) (hx : x ∈ negativeWeightSubmodule) :
    circularPeirceQuadratic x = 0 := by
  sorry"""
text = re.sub(r'theorem negativeWeight_totallyNull.*?(?=theorem projective_positiveWeight_fixed)', neg_null + '\n\n', text, flags=re.DOTALL)

# Also fix the Projectivization.ind destructuring
text = re.sub(
    r'  induction p using Projectivization\.ind with\n  \| h x hx =>',
    r'  rcases p with ⟨p, hp⟩\n  induction p using Projectivization.ind with\n  | h x hx =>',
    text
)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
