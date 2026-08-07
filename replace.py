import re

file_path = "/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean"
with open(file_path, "r") as f:
    content = f.read()

content = re.sub(
    r"ι_gamma_swap Q (\d) (\d) \(by decide\)",
    r"ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) \1 \2 (by decide))",
    content
)

content = re.sub(
    r"ι_gamma_sq Q (\d)",
    r"ι_sq_scalar Q (gamma Q \1)",
    content
)

with open(file_path, "w") as f:
    f.write(content)
