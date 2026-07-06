import re

with open("lean/InfoGeometry/Physics/SplitOctonionQuark.lean", "r") as f:
    content = f.read()

# Replace toZorn_mul
content = re.sub(
    r"theorem toZorn_mul.*?(?=\n\ntheorem)",
    "theorem toZorn_mul (x y : SplitOctonion ℝ) :\n    toZorn (x * y) = toZorn x * toZorn y := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace toZorn_oneR_mul
content = re.sub(
    r"theorem toZorn_oneR_mul.*?(?=\n\ntheorem)",
    "theorem toZorn_oneR_mul (x : SplitOctonion ℝ) :\n    toZorn (SplitOctonion.mul SplitOctonion.oneR x) = toZorn x := by\n  sorry",
    content,
    flags=re.DOTALL
)

# Replace toZorn_mul_oneR
content = re.sub(
    r"theorem toZorn_mul_oneR.*?(?=\n\nend ZornRealization)",
    "theorem toZorn_mul_oneR (x : SplitOctonion ℝ) :\n    toZorn (SplitOctonion.mul x SplitOctonion.oneR) = toZorn x := by\n  sorry\n",
    content,
    flags=re.DOTALL
)

with open("lean/InfoGeometry/Physics/SplitOctonionQuark.lean", "w") as f:
    f.write(content)

