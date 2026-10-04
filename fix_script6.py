with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "r") as f:
    content = f.read()

old_proof = """theorem associator_swap_cyclic (u v w : V) : blade3 R u v w = - blade3 R u w v := by
  unfold blade3
  have h1 : blade1 R u * blade1 R v * blade1 R w = blade1 R u * (blade1 R v * blade1 R w) := by rw [mul_assoc]
  have h2 : blade1 R u * blade1 R w * blade1 R v = blade1 R u * (blade1 R w * blade1 R v) := by rw [mul_assoc]
  rw [h1, h2, blade1_swap_neg R v w, mul_neg, neg_mul]"""

new_proof = """theorem associator_swap_cyclic (u v w : V) : blade3 R u v w = - blade3 R u w v := by
  unfold blade3
  have h1 : blade1 R u * blade1 R v * blade1 R w = blade1 R u * (blade1 R v * blade1 R w) := by rw [mul_assoc]
  have h2 : blade1 R u * blade1 R w * blade1 R v = blade1 R u * (blade1 R w * blade1 R v) := by rw [mul_assoc]
  rw [h1, h2, blade1_swap_neg R v w]
  simp only [mul_neg]"""

content = content.replace(old_proof, new_proof)

with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "w") as f:
    f.write(content)
