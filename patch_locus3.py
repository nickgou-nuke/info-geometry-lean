import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

# Replace induction
text = re.sub(
    r'  induction p using Projectivization\.ind with\n  \| h x hx =>',
    r'  rcases p with ⟨p, hp⟩\n  induction p using Projectivization.ind with\n  | h x hx =>',
    text
)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
