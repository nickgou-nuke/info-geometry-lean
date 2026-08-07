import os

file_path = "lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean"
with open(file_path, "r") as f:
    lines = f.readlines()

def replace_block(start_str, end_str, new_lines):
    start_idx = -1
    end_idx = -1
    for i, l in enumerate(lines):
        if start_str in l:
            start_idx = i
        if end_str in l and start_idx != -1 and end_idx == -1:
            end_idx = i
    
    if start_idx != -1 and end_idx != -1:
        lines[start_idx:end_idx+1] = new_lines

case2 = """    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h30]
        _ = - ((ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h20]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h31]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by rw [← Algebra.commutes]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := rfl
"""

case3 = """    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = - ((ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h30]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [sq1]
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1))) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)))) := by rw [← Algebra.commutes]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [mul_comm (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := rfl
"""

case4 = """    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h20]
        _ = - ((ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h10]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h21]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [sq1]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2))) * ι Q (gamma Q 3)) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * ι Q (gamma Q 0) * ι Q (gamma Q 3)) := by rw [← Algebra.commutes]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := rfl
"""

# Replace all failing cases
replace_block("have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) *", "_ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := rfl", case2.splitlines(True))
replace_block("have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) *", "_ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := rfl", case3.splitlines(True))
replace_block("have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) *", "_ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := rfl", case4.splitlines(True))

with open(file_path, "w") as f:
    f.writelines(lines)

print("Applied strict replacement.")
