import os

file_path = "lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean"
with open(file_path, "r") as f:
    content = f.read()

# I will replace the failing target 2
target2 = """        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3)))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ((ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)))) := by rw [← Algebra.commutes]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]"""

replacement2 = """        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ((ι Q (gamma Q 1) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)))) := by rw [algebraMap_comm_left]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]"""

target3 = """        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by rw [← Algebra.commutes]"""

replacement3 = """        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by rw [algebraMap_comm_left]"""

target4 = """        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3)))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3)))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)))) := by rw [← Algebra.commutes]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]"""

replacement4 = """        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)))) := by rw [algebraMap_comm_left]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]"""


content = content.replace(target2, replacement2)
content = content.replace(target3, replacement3)
content = content.replace(target4, replacement4)

with open(file_path, "w") as f:
    f.write(content)
