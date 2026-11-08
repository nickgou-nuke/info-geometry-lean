import re

with open("lean/InfoGeometry/Algebra/ZornVectorMatrix.lean", "r") as f:
    text = f.read()

# Fix 1: (add_smul (r := r) (s := s) (D := D))
text = text.replace(
    "change (r + s) • D = r • D + s • D\n    simpa using (add_smul (r := r) (s := s) (D := D)))",
    "change (r + s) • D = r • D + s • D\n    exact add_smul (r := r) (s := s) (D := D))"
)

# Fix 2: (zero_smul (D := D))
text = text.replace(
    "change (0 : R) • D = 0\n    simpa using (zero_smul (D := D)))",
    "change (0 : R) • D = 0\n    exact zero_smul (D := D))"
)

# Fix 3: bracket_skew
text = text.replace(
    "simpa [neg_eq_smul_neg_one] using congrArg (bracket E) (bracket_skew F D)",
    "simp only [neg_eq_smul_neg_one]\n          exact congrArg (bracket E) (bracket_skew F D)"
)

# Fix 4: bracket_smul_right (-1 : R)
text = text.replace(
    "simpa using (bracket_smul_right (-1 : R) E (bracket D F))",
    "exact (bracket_smul_right (-1 : R) E (bracket D F))"
)

# Fix 5: bracket_skew F
text = text.replace(
    "simpa using (bracket_skew F (bracket D E))",
    "exact (bracket_skew F (bracket D E))"
)

# Fix 6: h0
text = text.replace(
    "simpa [add_assoc, add_left_comm, add_comm] using h0",
    "change _ = 0 at h0\n        simp [add_assoc, add_left_comm, add_comm] at h0\n        exact h0"
)

# Fix 7: h'
text = text.replace(
    "simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'",
    "change _ = 0 at h'\n      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] at h'\n      exact h'"
)

# Fix 8: bracket_smul_right t D E
text = text.replace(
    "simpa using (bracket_smul_right t D E))",
    "exact (bracket_smul_right t D E))"
)

with open("lean/InfoGeometry/Algebra/ZornVectorMatrix.lean", "w") as f:
    f.write(text)

